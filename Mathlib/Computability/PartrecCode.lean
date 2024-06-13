/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Computability.Partrec
import Mathlib.Data.Option.Basic
import Batteries.Tactic.SqueezeScope

#align_import computability.partrec_code from "leanprover-community/mathlib"@"6155d4351090a6fad236e3d2e4e0e4e7342668e8"

/-!
# Gödel Numbering for Partial Recursive Functions.

This file defines `Nat.Partrec.Code`, an inductive datatype describing code for partial
recursive functions on ℕ. It defines an encoding for these codes, and proves that the constructors
are primitive recursive with respect to the encoding.

It also defines the evaluation of these codes as partial functions using `PFun`, and proves that a
function is partially recursive (as defined by `Nat.Partrec`) if and only if it is the evaluation
of some code.

## Main Definitions

* `Nat.Partrec.Code`: Inductive datatype for partial recursive codes.
* `Nat.Partrec.Code.encodeCode`: A (computable) encoding of codes as natural numbers.
* `Nat.Partrec.Code.ofNatCode`: The inverse of this encoding.
* `Nat.Partrec.Code.eval`: The interpretation of a `Nat.Partrec.Code` as a partial function.

## Main Results

* `Nat.Partrec.Code.rec_prim`: Recursion on `Nat.Partrec.Code` is primitive recursive.
* `Nat.Partrec.Code.rec_computable`: Recursion on `Nat.Partrec.Code` is computable.
* `Nat.Partrec.Code.smn`: The $S_n^m$ theorem.
* `Nat.Partrec.Code.exists_code`: Partial recursiveness is equivalent to being the eval of a code.
* `Nat.Partrec.Code.evaln_prim`: `evaln` is primitive recursive.
* `Nat.Partrec.Code.fixed_point`: Roger's fixed point theorem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]

-/


open Encodable Denumerable

namespace Nat.Partrec

theorem rfind' {f} (hf : Nat.Partrec f) : Nat.Partrec (Nat.unpaired fun a m =>
    (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m)) := by
  refine Partrec.unpaired'.2 <|
    ((@Partrec.unpaired' fun a b : ℕ =>
        Nat.rfind fun n => (· = 0) <$> f (Nat.pair a (n + b))).1 ?_).map
    (Primrec.nat_add.comp₂ Primrec.snd <| Primrec.snd.comp Primrec.fst).to_comp.to₂
  simpa using rfind <| Partrec.unpaired'.2 <| Partrec.to₂ <|
    (Partrec.nat_iff.2 hf).comp <| Primrec.to_comp <|
    Primrec.natPair.comp₂
      (Primrec.fst.comp <| Primrec.unpair.comp Primrec.fst)
      (Primrec.nat_add.comp₂ Primrec.snd
        (Primrec.snd.comp <| Primrec.unpair.comp Primrec.fst))
#align nat.partrec.rfind' Nat.Partrec.rfind'

/-- Code for partial recursive functions from ℕ to ℕ.
See `Nat.Partrec.Code.eval` for the interpretation of these constructors.
-/
inductive Code : Type
  | zero : Code
  | succ : Code
  | left : Code
  | right : Code
  | pair : Code → Code → Code
  | comp : Code → Code → Code
  | prec : Code → Code → Code
  | rfind' : Code → Code
#align nat.partrec.code Nat.Partrec.Code

-- Porting note: `Nat.Partrec.Code.recOn` is noncomputable in Lean4, so we make it computable.
compile_inductive% Code

end Nat.Partrec

namespace Nat.Partrec.Code

instance instInhabited : Inhabited Code :=
  ⟨zero⟩
#align nat.partrec.code.inhabited Nat.Partrec.Code.instInhabited

/-- Returns a code for the constant function outputting a particular natural. -/
protected def const : ℕ → Code
  | 0 => zero
  | n + 1 => comp succ (Code.const n)
#align nat.partrec.code.const Nat.Partrec.Code.const

theorem const_inj : ∀ {n₁ n₂}, Nat.Partrec.Code.const n₁ = Nat.Partrec.Code.const n₂ → n₁ = n₂
  | 0, 0, _ => by simp
  | n₁ + 1, n₂ + 1, h => by
    dsimp [Nat.Partrec.Code.const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]
#align nat.partrec.code.const_inj Nat.Partrec.Code.const_inj

/-- A code for the identity function. -/
protected def id : Code :=
  pair left right
#align nat.partrec.code.id Nat.Partrec.Code.id

/-- Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
def curry (c : Code) (n : ℕ) : Code :=
  comp c (pair (Code.const n) Code.id)
#align nat.partrec.code.curry Nat.Partrec.Code.curry

-- Porting note: `bit0` and `bit1` are deprecated.
/-- An encoding of a `Nat.Partrec.Code` as a ℕ. -/
def encodeCode : Code → ℕ
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | pair cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 4
  | comp cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 4
  | prec cf cg => (2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 1) + 4
  | rfind' cf => (2 * (2 * encodeCode cf + 1) + 1) + 4
#align nat.partrec.code.encode_code Nat.Partrec.Code.encodeCode

/--
A decoder for `Nat.Partrec.Code.encodeCode`, taking any ℕ to the `Nat.Partrec.Code` it represents.
-/
def ofNatCode : ℕ → Code
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | n + 4 =>
    let m := n.div2.div2
    have hm : m < n + 4 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => pair (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | false, true  => comp (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true , false => prec (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true , true  => rfind' (ofNatCode m)
#align nat.partrec.code.of_nat_code Nat.Partrec.Code.ofNatCode

/-- Proof that `Nat.Partrec.Code.ofNatCode` is the inverse of `Nat.Partrec.Code.encodeCode`-/
private theorem encode_ofNatCode : ∀ n, encodeCode (ofNatCode n) = n
  | 0 => by simp [ofNatCode, encodeCode]
  | 1 => by simp [ofNatCode, encodeCode]
  | 2 => by simp [ofNatCode, encodeCode]
  | 3 => by simp [ofNatCode, encodeCode]
  | n + 4 => by
    let m := n.div2.div2
    have hm : m < n + 4 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode_ofNatCode m
    have IH1 := encode_ofNatCode m.unpair.1
    have IH2 := encode_ofNatCode m.unpair.2
    conv_rhs => rw [← Nat.bit_decomp n, ← Nat.bit_decomp n.div2]
    simp only [ofNatCode.eq_5]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [encodeCode, ofNatCode, IH, IH1, IH2, Nat.bit_val]

instance instDenumerable : Denumerable Code :=
  mk'
    ⟨encodeCode, ofNatCode, fun c => by
        induction c <;> try {rfl} <;> simp [encodeCode, ofNatCode, Nat.div2_val, *],
      encode_ofNatCode⟩
#align nat.partrec.code.denumerable Nat.Partrec.Code.instDenumerable

theorem encodeCode_eq : encode = encodeCode :=
  rfl
#align nat.partrec.code.encode_code_eq Nat.Partrec.Code.encodeCode_eq

theorem ofNatCode_eq : ofNat Code = ofNatCode :=
  rfl
#align nat.partrec.code.of_nat_code_eq Nat.Partrec.Code.ofNatCode_eq

theorem encode_lt_pair (cf cg) :
    encode cf < encode (pair cf cg) ∧ encode cg < encode (pair cf cg) := by
  simp only [encodeCode_eq, encodeCode]
  have := Nat.mul_le_mul_right (Nat.pair cf.encodeCode cg.encodeCode) (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 4))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) this, lt_of_le_of_lt (Nat.right_le_pair _ _) this⟩
#align nat.partrec.code.encode_lt_pair Nat.Partrec.Code.encode_lt_pair

theorem encode_lt_comp (cf cg) :
    encode cf < encode (comp cf cg) ∧ encode cg < encode (comp cf cg) := by
  have : encode (pair cf cg) < encode (comp cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this
#align nat.partrec.code.encode_lt_comp Nat.Partrec.Code.encode_lt_comp

theorem encode_lt_prec (cf cg) :
    encode cf < encode (prec cf cg) ∧ encode cg < encode (prec cf cg) := by
  have : encode (pair cf cg) < encode (prec cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this
#align nat.partrec.code.encode_lt_prec Nat.Partrec.Code.encode_lt_prec

theorem encode_lt_rfind' (cf) : encode cf < encode (rfind' cf) := by
  simp only [encodeCode_eq, encodeCode]
  have := Nat.mul_le_mul_right cf.encodeCode (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc] at this
  refine lt_of_le_of_lt (le_trans this ?_) (lt_add_of_pos_right _ (by decide : 0 < 4))
  exact le_of_lt (Nat.lt_succ_of_le <| Nat.mul_le_mul_left _ <| le_of_lt <|
    Nat.lt_succ_of_le <| Nat.mul_le_mul_left _ <| le_rfl)
#align nat.partrec.code.encode_lt_rfind' Nat.Partrec.Code.encode_lt_rfind'

end Nat.Partrec.Code

-- Porting note: Opening `Primrec` inside `namespace Nat.Partrec.Code` causes it to resolve
-- to `Nat.Partrec`. Needs `open _root_.Partrec` support
section
open Primrec
namespace Nat.Partrec.Code

theorem pair_prim : Primrec₂ pair :=
  Primrec.ofNat_iff₂.2 <| Primrec.encode_iff.1 <| nat_add.comp₂
    (nat_double.comp <| nat_double.comp <| Primrec.natPair.comp₂
      (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
      (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
    (.const 4)
#align nat.partrec.code.pair_prim Nat.Partrec.Code.pair_prim

theorem comp_prim : Primrec₂ comp :=
  Primrec.ofNat_iff₂.2 <| Primrec.encode_iff.1 <| nat_add.comp₂
    (nat_double.comp <| nat_double_succ.comp <| Primrec.natPair.comp₂
      (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
      (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
    (.const 4)
#align nat.partrec.code.comp_prim Nat.Partrec.Code.comp_prim

theorem prec_prim : Primrec₂ prec :=
  Primrec.ofNat_iff₂.2 <| Primrec.encode_iff.1 <| nat_add.comp₂
    (nat_double_succ.comp <| nat_double.comp <| Primrec.natPair.comp₂
        (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
        (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
    (.const 4)
#align nat.partrec.code.prec_prim Nat.Partrec.Code.prec_prim

theorem rfind_prim : Primrec rfind' :=
  ofNat_iff.2 <| encode_iff.1 <| nat_add.comp₂
    (nat_double_succ.comp <| nat_double_succ.comp <|
      encode_iff.2 <| Primrec.ofNat Code)
    (const 4)
#align nat.partrec.code.rfind_prim Nat.Partrec.Code.rfind_prim

theorem rec_prim' {α σ} [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {pr : α → Code × Code × σ × σ → σ} (hpr : Primrec₂ pr)
    {co : α → Code × Code × σ × σ → σ} (hco : Primrec₂ co) {pc : α → Code × Code × σ × σ → σ}
    (hpc : Primrec₂ pc) {rf : α → Code × σ → σ} (hrf : Primrec₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a)
    Primrec (fun a => F a (c a) : α → σ) := by
  intros _ _ _ _ F
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    letI a := p.1.1; letI IH := p.1.2; letI n := p.2.1; letI m := p.2.2
    (IH.get? m).bind fun s =>
    (IH.get? m.unpair.1).bind fun s₁ =>
    (IH.get? m.unpair.2).map fun s₂ =>
    cond n.bodd
      (cond n.div2.bodd (rf a (ofNat Code m, s))
        (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
        (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  have : Primrec G₁ :=
    option_bind (list_get?.comp₂ (snd.comp fst) (snd.comp snd)) <| .to₂ <|
    option_bind ((list_get?.comp₂ (snd.comp fst)
      (fst.comp <| Primrec.unpair.comp (snd.comp snd))).comp fst) <| .to₂ <|
    option_map ((list_get?.comp₂ (snd.comp fst)
      (snd.comp <| Primrec.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .to₂ <|
    have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
    have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m₁ := fst.comp (Primrec.unpair.comp m)
    have m₂ := snd.comp (Primrec.unpair.comp m)
    have s := snd.comp (fst.comp fst)
    have s₁ := snd.comp fst
    have s₂ := snd
    (nat_bodd.comp n).cond
      ((nat_bodd.comp <| nat_div2.comp n).cond
        (hrf.comp₂ a (((Primrec.ofNat Code).comp m).pair s))
        (hpc.comp₂ a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
      (Primrec.cond (nat_bodd.comp <| nat_div2.comp n)
        (hco.comp₂ a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂))
        (hpr.comp₂ a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.casesOn (some (z a)) fun n =>
    n.casesOn (some (s a)) fun n =>
    n.casesOn (some (l a)) fun n =>
    n.casesOn (some (r a)) fun n =>
    G₁ ((a, IH), n, n.div2.div2)
  have' : Primrec₂ G := .to₂ <|
    nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <| .to₂ <|
    nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) <| .to₂ <|
    nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <| .to₂ <|
    nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) <| .to₂ <|
    this.comp <|
      ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
      snd.pair <| nat_div2.comp <| nat_div2.comp snd
  refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
    |>.comp₂ .id (encode_iff.2 hc) |>.of_eq fun a => by simp
  iterate 4 cases' n with n <;> [(simp [ofNatCode_eq, ofNatCode]; rfl); skip]
  simp only [G]; rw [List.length_map, List.length_range]
  let m := n.div2.div2
  show G₁ ((a, (List.range (n + 4)).map fun n => F a (ofNat Code n)), n, m)
    = some (F a (ofNat Code (n + 4)))
  have hm : m < n + 4 := by
    simp only [m, div2_val]
    exact lt_of_le_of_lt
      (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
      (Nat.succ_le_succ (Nat.le_add_right ..))
  have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
  simp only [List.get?_map, G₁, hm, List.get?_range, m1, m2, m]
  rw [show ofNat Code (n + 4) = ofNatCode (n + 4) from rfl]
  simp only [ofNatCode]
  cases n.bodd <;> cases n.div2.bodd <;> rfl
#align nat.partrec.code.rec_prim' Nat.Partrec.Code.rec_prim'

/-- Recursion on `Nat.Partrec.Code` is primitive recursive. -/
theorem rec_prim {α σ} [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {pr : α → Code → Code → σ → σ → σ}
    (hpr : Primrec fun a : α × Code × Code × σ × σ => pr a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {co : α → Code → Code → σ → σ → σ}
    (hco : Primrec fun a : α × Code × Code × σ × σ => co a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {pc : α → Code → Code → σ → σ → σ}
    (hpc : Primrec fun a : α × Code × Code × σ × σ => pc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {rf : α → Code → σ → σ} (hrf : Primrec fun a : α × Code × σ => rf a.1 a.2.1 a.2.2) :
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (pr a) (co a) (pc a) (rf a)
    Primrec fun a => F a (c a) :=
  rec_prim' hc hz hs hl hr
    (pr := fun a b => pr a b.1 b.2.1 b.2.2.1 b.2.2.2) hpr.to₂
    (co := fun a b => co a b.1 b.2.1 b.2.2.1 b.2.2.2) hco.to₂
    (pc := fun a b => pc a b.1 b.2.1 b.2.2.1 b.2.2.2) hpc.to₂
    (rf := fun a b => rf a b.1 b.2) hrf.to₂
#align nat.partrec.code.rec_prim Nat.Partrec.Code.rec_prim

end Nat.Partrec.Code
end

namespace Nat.Partrec.Code
section

open Computable

/-- Recursion on `Nat.Partrec.Code` is computable. -/
theorem rec_computable {α σ} [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Computable c)
    {z : α → σ} (hz : Computable z) {s : α → σ} (hs : Computable s) {l : α → σ} (hl : Computable l)
    {r : α → σ} (hr : Computable r) {pr : α → Code × Code × σ × σ → σ} (hpr : Computable₂ pr)
    {co : α → Code × Code × σ × σ → σ} (hco : Computable₂ co) {pc : α → Code × Code × σ × σ → σ}
    (hpc : Computable₂ pc) {rf : α → Code × σ → σ} (hrf : Computable₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Nat.Partrec.Code.recOn c (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a)
    Computable fun a => F a (c a) := by
  -- TODO(Mario): less copy-paste from previous proof
  intros _ _ _ _ F
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    letI a := p.1.1; letI IH := p.1.2; letI n := p.2.1; letI m := p.2.2
    (IH.get? m).bind fun s =>
    (IH.get? m.unpair.1).bind fun s₁ =>
    (IH.get? m.unpair.2).map fun s₂ =>
    cond n.bodd
      (cond n.div2.bodd (rf a (ofNat Code m, s))
        (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
        (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  have' : Computable (_ :  (α × List σ) × ℕ × ℕ → Option σ) :=
    option_bind (list_get?.comp₂ (snd.comp fst) (snd.comp snd)) <| .to₂ <|
    option_bind ((list_get?.comp₂ (snd.comp fst)
      (fst.comp <| Computable.unpair.comp (snd.comp snd))).comp fst) <| .to₂ <|
    option_map ((list_get?.comp₂ (snd.comp fst)
      (snd.comp <| Computable.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .to₂ <|
    have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
    have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m₁ := fst.comp (Computable.unpair.comp m)
    have m₂ := snd.comp (Computable.unpair.comp m)
    have s := snd.comp (fst.comp fst)
    have s₁ := snd.comp fst
    have s₂ := snd
    (nat_bodd.comp n).cond
      ((nat_bodd.comp <| nat_div2.comp n).cond
        (hrf.comp₂ a (((Computable.ofNat Code).comp m).pair s))
        (hpc.comp₂ a (((Computable.ofNat Code).comp m₁).pair <|
          ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
      (Computable.cond (nat_bodd.comp <| nat_div2.comp n)
        (hco.comp₂ a (((Computable.ofNat Code).comp m₁).pair <|
          ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂))
        (hpr.comp₂ a (((Computable.ofNat Code).comp m₁).pair <|
          ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.casesOn (some (z a)) fun n =>
    n.casesOn (some (s a)) fun n =>
    n.casesOn (some (l a)) fun n =>
    n.casesOn (some (r a)) fun n =>
    G₁ ((a, IH), n, n.div2.div2)
  have : Computable₂ G := .to₂ <|
    nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <| .to₂ <|
    nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) <| .to₂ <|
    nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <| .to₂ <|
    nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) <| .to₂ <|
    this.comp <|
      ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
      snd.pair <| nat_div2.comp <| nat_div2.comp snd
  refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
    |>.comp₂ .id (encode_iff.2 hc) |>.of_eq fun a => by simp
  iterate 4 cases' n with n <;> [(simp [ofNatCode_eq, ofNatCode]; rfl); skip]
  simp only [G]; rw [List.length_map, List.length_range]
  let m := n.div2.div2
  show G₁ ((a, (List.range (n + 4)).map fun n => F a (ofNat Code n)), n, m)
    = some (F a (ofNat Code (n + 4)))
  have hm : m < n + 4 := by
    simp only [m, div2_val]
    exact lt_of_le_of_lt
      (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
      (Nat.succ_le_succ (Nat.le_add_right ..))
  have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
  simp only [List.get?_map, G₁, hm, List.get?_range, m1, m2, m]
  rw [show ofNat Code (n + 4) = ofNatCode (n + 4) from rfl]
  simp only [ofNatCode]
  cases n.bodd <;> cases n.div2.bodd <;> rfl
#align nat.partrec.code.rec_computable Nat.Partrec.Code.rec_computable

end

/-- The interpretation of a `Nat.Partrec.Code` as a partial function.
* `Nat.Partrec.Code.zero`: The constant zero function.
* `Nat.Partrec.Code.succ`: The successor function.
* `Nat.Partrec.Code.left`: Left unpairing of a pair of ℕ (encoded by `Nat.pair`)
* `Nat.Partrec.Code.right`: Right unpairing of a pair of ℕ (encoded by `Nat.pair`)
* `Nat.Partrec.Code.pair`: Pairs the outputs of argument codes using `Nat.pair`.
* `Nat.Partrec.Code.comp`: Composition of two argument codes.
* `Nat.Partrec.Code.prec`: Primitive recursion. Given an argument of the form `Nat.pair a n`:
  * If `n = 0`, returns `eval cf a`.
  * If `n = succ k`, returns `eval cg (pair a (pair k (eval (prec cf cg) (pair a k))))`
* `Nat.Partrec.Code.rfind'`: Minimization. For `f` an argument of the form `Nat.pair a m`,
  `rfind' f m` returns the least `a` such that `f a m = 0`, if one exists and `f b m` terminates
  for `b < a`
-/
def eval : Code → ℕ →. ℕ
  | zero => pure 0
  | succ => Nat.succ
  | left => ↑fun n : ℕ => n.unpair.1
  | right => ↑fun n : ℕ => n.unpair.2
  | pair cf cg => fun n => Nat.pair <$> eval cf n <*> eval cg n
  | comp cf cg => fun n => eval cg n >>= eval cf
  | prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (eval cf a) fun y IH => do
        let i ← IH
        eval cg (Nat.pair a (Nat.pair y i))
  | rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> eval cf (Nat.pair a (n + m))).map (· + m)
#align nat.partrec.code.eval Nat.Partrec.Code.eval

/-- Helper lemma for the evaluation of `prec` in the base case. -/
@[simp]
theorem eval_prec_zero (cf cg : Code) (a : ℕ) : eval (prec cf cg) (Nat.pair a 0) = eval cf a := by
  rw [eval, Nat.unpaired, Nat.unpair_pair, Nat.rec_zero]
#align nat.partrec.code.eval_prec_zero Nat.Partrec.Code.eval_prec_zero

/-- Helper lemma for the evaluation of `prec` in the recursive case. -/
theorem eval_prec_succ (cf cg : Code) (a k : ℕ) :
    eval (prec cf cg) (Nat.pair a (Nat.succ k)) =
      do {let ih ← eval (prec cf cg) (Nat.pair a k); eval cg (Nat.pair a (Nat.pair k ih))} := by
  rw [eval, Nat.unpaired, Part.bind_eq_bind, Nat.unpair_pair]
  simp
#align nat.partrec.code.eval_prec_succ Nat.Partrec.Code.eval_prec_succ

instance : Membership (ℕ →. ℕ) Code :=
  ⟨fun f c => eval c = f⟩

@[simp]
theorem eval_const : ∀ n m, eval (Code.const n) m = Part.some n
  | 0, m => rfl
  | n + 1, m => by simp [eval, eval_const n m]
#align nat.partrec.code.eval_const Nat.Partrec.Code.eval_const

@[simp]
theorem eval_id (n) : eval Code.id n = Part.some n := by simp [eval, Seq.seq]
#align nat.partrec.code.eval_id Nat.Partrec.Code.eval_id

@[simp]
theorem eval_curry (c n x) : eval (curry c n) x = eval c (Nat.pair n x) := by simp [eval, Seq.seq]
#align nat.partrec.code.eval_curry Nat.Partrec.Code.eval_curry

theorem const_prim : Primrec Code.const :=
  _root_.Primrec.id.nat_iterate (.const zero) (comp_prim.comp₂ (.const succ) Primrec.snd).to₂
  |>.of_eq fun n => by
    simp only [id_eq]
    induction n <;>
      simp [*, Code.const, Function.iterate_succ', -Function.iterate_succ]
#align nat.partrec.code.const_prim Nat.Partrec.Code.const_prim

theorem curry_prim : Primrec₂ curry :=
  comp_prim.comp₂ Primrec.fst <| pair_prim.comp₂ (const_prim.comp Primrec.snd)
    (_root_.Primrec.const Code.id)
#align nat.partrec.code.curry_prim Nat.Partrec.Code.curry_prim

theorem curry_inj {c₁ c₂ n₁ n₂} (h : curry c₁ n₁ = curry c₂ n₂) : c₁ = c₂ ∧ n₁ = n₂ :=
  ⟨by injection h, by
    injection h with h₁ h₂
    injection h₂ with h₃ h₄
    exact const_inj h₃⟩
#align nat.partrec.code.curry_inj Nat.Partrec.Code.curry_inj

/--
The $S_n^m$ theorem: There is a computable function, namely `Nat.Partrec.Code.curry`, that takes a
program and a ℕ `n`, and returns a new program using `n` as the first argument.
-/
theorem smn :
    ∃ f : Code → ℕ → Code, Computable₂ f ∧ ∀ c n x, eval (f c n) x = eval c (Nat.pair n x) :=
  ⟨curry, curry_prim.to_comp, eval_curry⟩
#align nat.partrec.code.smn Nat.Partrec.Code.smn

/-- A function is partial recursive if and only if there is a code implementing it. Therefore,
`eval` is a **universal partial recursive function**. -/
theorem exists_code {f : ℕ →. ℕ} : Nat.Partrec f ↔ ∃ c : Code, eval c = f := by
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | zero => exact ⟨zero, rfl⟩
    | succ => exact ⟨succ, rfl⟩
    | left => exact ⟨left, rfl⟩
    | right => exact ⟨right, rfl⟩
    | pair pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨pair cf cg, rfl⟩
    | comp pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨comp cf cg, rfl⟩
    | prec pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨prec cf cg, rfl⟩
    | rfind pf hf =>
      rcases hf with ⟨cf, rfl⟩
      refine ⟨comp (rfind' cf) (pair Code.id zero), ?_⟩
      simp [eval, Seq.seq, pure, PFun.pure, Part.map_id']
  · rintro ⟨c, rfl⟩
    induction c with
    | zero => exact Nat.Partrec.zero
    | succ => exact Nat.Partrec.succ
    | left => exact Nat.Partrec.left
    | right => exact Nat.Partrec.right
    | pair cf cg pf pg => exact pf.pair pg
    | comp cf cg pf pg => exact pf.comp pg
    | prec cf cg pf pg => exact pf.prec pg
    | rfind' cf pf => exact pf.rfind'
#align nat.partrec.code.exists_code Nat.Partrec.Code.exists_code

-- Porting note: `>>`s in `evaln` are now `>>=` because `>>`s are not elaborated well in Lean4.
/-- A modified evaluation for the code which returns an `Option ℕ` instead of a `Part ℕ`. To avoid
undecidability, `evaln` takes a parameter `k` and fails if it encounters a number ≥ k in the course
of its execution. Other than this, the semantics are the same as in `Nat.Partrec.Code.eval`.
-/
def evaln : ℕ → Code → ℕ → Option ℕ
  | 0, _ => fun _ => Option.none
  | k + 1, zero => fun n => do
    guard (n ≤ k)
    return 0
  | k + 1, succ => fun n => do
    guard (n ≤ k)
    return (Nat.succ n)
  | k + 1, left => fun n => do
    guard (n ≤ k)
    return n.unpair.1
  | k + 1, right => fun n => do
    guard (n ≤ k)
    pure n.unpair.2
  | k + 1, pair cf cg => fun n => do
    guard (n ≤ k)
    Nat.pair <$> evaln (k + 1) cf n <*> evaln (k + 1) cg n
  | k + 1, comp cf cg => fun n => do
    guard (n ≤ k)
    let x ← evaln (k + 1) cg n
    evaln (k + 1) cf x
  | k + 1, prec cf cg => fun n => do
    guard (n ≤ k)
    n.unpaired fun a n =>
      n.casesOn (evaln (k + 1) cf a) fun y => do
        let i ← evaln k (prec cf cg) (Nat.pair a y)
        evaln (k + 1) cg (Nat.pair a (Nat.pair y i))
  | k + 1, rfind' cf => fun n => do
    guard (n ≤ k)
    n.unpaired fun a m => do
      let x ← evaln (k + 1) cf (Nat.pair a m)
      if x = 0 then
        pure m
      else
        evaln k (rfind' cf) (Nat.pair a (m + 1))
#align nat.partrec.code.evaln Nat.Partrec.Code.evaln

theorem evaln_bound : ∀ {k c n x}, x ∈ evaln k c n → n < k
  | 0, c, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    suffices ∀ {o : Option ℕ}, x ∈ do { guard (n ≤ k); o } → n < k + 1 by
      cases c <;> rw [evaln] at h <;> exact this h
    simpa [Option.bind_eq_some] using Nat.lt_succ_of_le
#align nat.partrec.code.evaln_bound Nat.Partrec.Code.evaln_bound

theorem evaln_mono : ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ → x ∈ evaln k₁ c n → x ∈ evaln k₂ c n
  | 0, k₂, c, n, x, _, h => by simp [evaln] at h
  | k + 1, k₂ + 1, c, n, x, hl, h => by
    have hl' := Nat.le_of_succ_le_succ hl
    have :
      ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
        k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) →
          x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k₂); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some, Option.guard_eq_some', exists_and_left,
        exists_const, and_imp]
      introv h h₁ h₂ h₃
      exact ⟨le_trans h₂ h, h₁ h₃⟩
    simp only [Option.mem_def] at h ⊢
    induction' c with cf cg hf hg cf cg hf hg cf cg hf hg cf hf generalizing x n <;>
      rw [evaln] at h ⊢ <;> refine this hl' (fun h => ?_) h
    iterate 4 exact h
    · -- pair cf cg
      simp only [Seq.seq, Option.map_eq_map, Option.mem_def, Option.bind_eq_some,
        Option.map_eq_some', exists_exists_and_eq_and] at h ⊢
      exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
    · -- comp cf cg
      simp only [bind, Option.mem_def, Option.bind_eq_some] at h ⊢
      exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    · -- prec cf cg
      revert h
      simp only [unpaired, bind, Option.mem_def]
      cases n.unpair.2 with
      | zero => apply hf
      | succ =>
        simp only [Option.bind_eq_some, rec_zero]
        exact fun ⟨y, h₁, h₂⟩ => ⟨y, evaln_mono hl' h₁, hg _ _ h₂⟩
    · -- rfind' cf
      simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
        Option.bind_eq_some] at h ⊢
      refine h.imp fun x => And.imp (hf _ _) ?_
      split_ifs <;> [apply id; exact evaln_mono hl']
#align nat.partrec.code.evaln_mono Nat.Partrec.Code.evaln_mono

theorem evaln_sound : ∀ {k c n x}, x ∈ evaln k c n → x ∈ eval c n
  | 0, _, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    induction c generalizing x n with
      simp [eval, evaln, Option.bind_eq_some, Seq.seq] at h ⊢ <;>
      cases' h with _ h
    | pair cf cg hf hg =>
      rcases h with ⟨y, ef, z, eg, rfl⟩
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    | comp cf cg hf hg =>
      rcases h with ⟨y, eg, ef⟩
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    | prec cf cg hf hg =>
      revert h
      induction n.unpair.2 generalizing x with simp [Option.bind_eq_some]
      | zero => apply hf
      | succ m IH =>
        refine fun y h₁ h₂ => ⟨y, IH _ ?_, hg _ _ h₂⟩
        have := evaln_mono k.le_succ h₁
        simp only [evaln, unpaired, unpair_pair, Option.bind_eq_bind,
          Option.mem_def, Option.bind_eq_some, Option.guard_eq_some', exists_const] at this
        exact this.2
    | rfind' cf hf =>
      let ⟨m, h₁, h₂⟩ := h
      split_ifs at h₂ with m0
      --  <;> simp only [m0, ↓reduceIte, Option.some.injEq] at h₂
      · cases h₂
        exact ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun {m} => (Nat.not_lt_zero _).elim⟩, by simp⟩
      · have := evaln_sound h₂
        simp only [eval, unpaired, unpair_pair, Part.map_eq_map, Part.mem_map_iff, mem_rfind,
          decide_eq_true_eq, exists_eq_right, decide_eq_false_iff_not] at this
        obtain ⟨y, ⟨hy₁, hy₂⟩, rfl⟩ := this
        refine ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun {i} im => ?_⟩, ?_⟩
        · match i with
          | 0 => exact ⟨m, by simpa using hf _ _ h₁, m0⟩
          | i+1 =>
            let ⟨z, hz, z0⟩ := hy₂ (Nat.lt_of_succ_lt_succ im)
            exact ⟨z, by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hz, z0⟩
        · simp [add_comm, add_left_comm]
    | _ => simpa [pure, PFun.pure, eq_comm] using h
#align nat.partrec.code.evaln_sound Nat.Partrec.Code.evaln_sound

theorem evaln_complete {c n x} : x ∈ eval c n ↔ ∃ k, x ∈ evaln k c n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => evaln_sound h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ evaln (k + 1) c n
  · exact ⟨k + 1, h⟩
  induction c generalizing n x with
    simp [eval, evaln, pure, PFun.pure, Seq.seq, Option.bind_eq_some] at h ⊢
  | pair cf cg hf hg =>
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
    rcases h with ⟨y, hy, hx⟩
    rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    exact
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂⟩
  | prec cf cg hf hg =>
    revert h
    generalize n.unpair.1 = n₁; generalize n.unpair.2 = n₂
    induction n₂ generalizing x n with
    | zero =>
      intro h
      rcases hf h with ⟨k, hk⟩
      exact ⟨_, le_max_left _ _, evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    | succ m IH =>
      simp only [Option.bind_eq_some, Part.mem_bind_iff]
      intro ⟨y, hy, hx⟩
      obtain ⟨k₁, nk₁, hk₁⟩ := IH hy
      let ⟨k₂, hk₂⟩ := hg hx
      refine
        ⟨(max k₁ k₂).succ,
          Nat.le_succ_of_le <| le_max_of_le_left <|
            le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁, y,
          evaln_mono (Nat.succ_le_succ <| le_max_left _ _) ?_,
          evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_right _ _) hk₂⟩
      simp only [evaln.eq_8, bind, unpaired, unpair_pair, Option.mem_def, Option.bind_eq_some,
        Option.guard_eq_some', exists_and_left, exists_const]
      exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩
  | rfind' cf hf =>
    rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    suffices ∃ k, y + n.unpair.2 ∈ evaln (k + 1) (rfind' cf) (Nat.pair n.unpair.1 n.unpair.2) by
      simpa [evaln, Option.bind_eq_some]
    revert hy₁ hy₂
    generalize n.unpair.2 = m
    intro hy₁ hy₂
    induction y generalizing m with
      simp only [evaln, unpair_pair, Option.bind_eq_bind, Option.mem_def,
        Option.bind_eq_some, Option.guard_eq_some', exists_const]
    | zero =>
      let ⟨k, hk⟩ := hf hy₁
      simp only [zero_add] at hk
      exact ⟨_, Nat.le_of_lt_succ <| evaln_bound hk, _, hk, by simp⟩
    | succ y IH =>
      let ⟨a, ha, a0⟩ := hy₂ (Nat.succ_pos _)
      let ⟨k₁, hk₁⟩ := hf ha
      let ⟨k₂, hk₂⟩ := IH m.succ
        (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
        (fun {i} hi => by
          simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₂ (Nat.succ_lt_succ hi))
      rw [zero_add] at hk₁
      refine ⟨(max k₁ k₂).succ, ?_, a, ?_, ?_⟩
      · exact Nat.le_succ_of_le <| le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁
      · exact evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
      · simpa [Nat.succ_eq_add_one, a0, -max_eq_left, -max_eq_right, add_comm, add_left_comm] using
          evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂
  | _ => exact ⟨⟨_, le_rfl⟩, h.symm⟩
#align nat.partrec.code.evaln_complete Nat.Partrec.Code.evaln_complete

section

open Primrec

private def lup (L : List (List (Option ℕ))) (p : ℕ × Code) (n : ℕ) := do
  let l ← L.get? (encode p)
  let o ← l.get? n
  o

private theorem hlup : Primrec fun p : _ × (_ × _) × _ => lup p.1 p.2.1 p.2.2 :=
  Primrec.option_bind
    (Primrec.list_get?.comp₂ Primrec.fst (Primrec.encode.comp <| Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind (Primrec.list_get?.comp₂ Primrec.snd <| Primrec.snd.comp <|
      Primrec.snd.comp Primrec.fst) Primrec.snd)

private def G (L : List (List (Option ℕ))) : Option (List (Option ℕ)) :=
  let a := ofNat (ℕ × Code) L.length
  let k := a.1; let c := a.2
  some <| (List.range k).map fun n =>
  k.casesOn Option.none fun k' =>
  Nat.Partrec.Code.recOn c
    (some 0) -- zero
    (some (Nat.succ n))
    (some n.unpair.1)
    (some n.unpair.2)
    (fun cf cg _ _ => return Nat.pair (← lup L (k, cf) n) (← lup L (k, cg) n))
    (fun cf cg _ _ => do lup L (k, cf) (← lup L (k, cg) n))
    (fun cf cg _ _ =>
      let z := n.unpair.1
      n.unpair.2.casesOn (lup L (k, cf) z) fun y => do
        lup L (k, cg) (Nat.pair z (Nat.pair y (← lup L (k', c) (Nat.pair z y)))))
    (fun cf _ => do
      let (z, m) := n.unpair
      (← lup L (k, cf) (Nat.pair z m)).casesOn (some m) fun _ =>
        lup L (k', c) (Nat.pair z (m + 1)))

private theorem hG : Primrec G := by
  have a := (Primrec.ofNat (ℕ × Code)).comp (Primrec.list_length (α := List (Option ℕ)))
  have k := Primrec.fst.comp a
  refine Primrec.option_some.comp <| Primrec.list_map (Primrec.list_range.comp k) ?_
  replace k := k.comp (Primrec.fst (β := ℕ))
  have n := Primrec.snd (α := List (List (Option ℕ))) (β := ℕ)
  refine Primrec.nat_casesOn k (_root_.Primrec.const Option.none) ?_
  have k := k.comp (Primrec.fst (β := ℕ))
  have n := n.comp (Primrec.fst (β := ℕ))
  have k' := Primrec.snd (α := List (List (Option ℕ)) × ℕ) (β := ℕ)
  have c := Primrec.snd.comp (a.comp <| (Primrec.fst (β := ℕ)).comp (Primrec.fst (β := ℕ)))
  apply Nat.Partrec.Code.rec_prim c
  · exact .const (some 0)
  · exact Primrec.option_some.comp (_root_.Primrec.succ.comp n)
  · exact Primrec.option_some.comp (Primrec.fst.comp <| Primrec.unpair.comp n)
  · exact Primrec.option_some.comp (Primrec.snd.comp <| Primrec.unpair.comp n)
  · simp only [Option.bind_eq_bind, bind_pure_comp, Option.map_eq_map]
    exact
      have L := (Primrec.fst.comp Primrec.fst).comp Primrec.fst
      have k := k.comp Primrec.fst
      have n := n.comp Primrec.fst
      have cf := Primrec.fst.comp Primrec.snd
      have cg := (Primrec.fst.comp Primrec.snd).comp Primrec.snd
      Primrec.option_bind (hlup.comp <| L.pair <| (k.pair cf).pair n)
      (Primrec.option_map ((hlup.comp <| L.pair <| (k.pair cg).pair n).comp Primrec.fst)
      (Primrec.natPair.comp₂ (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  · exact
      have L := (Primrec.fst.comp Primrec.fst).comp Primrec.fst
      have k := k.comp Primrec.fst
      have n := n.comp Primrec.fst
      have cf := Primrec.fst.comp Primrec.snd
      have cg := (Primrec.fst.comp Primrec.snd).comp Primrec.snd
      Primrec.option_bind (hlup.comp <| L.pair <| (k.pair cg).pair n) <|
      (hlup.comp <| (L.comp Primrec.fst).pair <|
        ((k.pair cf).comp Primrec.fst).pair Primrec.snd).to₂
  · exact
      have L := (Primrec.fst.comp Primrec.fst).comp Primrec.fst
      have k := k.comp Primrec.fst
      have n := Primrec.unpair.comp (n.comp Primrec.fst)
      have cf := Primrec.fst.comp Primrec.snd
      have cg := (Primrec.fst.comp Primrec.snd).comp Primrec.snd
      have z := Primrec.fst.comp n
      Primrec.nat_casesOn (Primrec.snd.comp n)
        (hlup.comp <| L.pair <| (k.pair cf).pair z) <|
      have L := L.comp Primrec.fst
      have z := z.comp Primrec.fst
      have y := Primrec.snd
      have h₁ := hlup.comp <| L.pair <| (((k'.pair c).comp Primrec.fst).comp Primrec.fst).pair
        (Primrec.natPair.comp₂ z y)
      Primrec.option_bind h₁ <|
      have z := z.comp Primrec.fst
      have y := y.comp Primrec.fst
      have i := Primrec.snd
      (hlup.comp ((L.comp Primrec.fst).pair <|
        ((k.pair cg).comp <| Primrec.fst.comp Primrec.fst).pair <|
          Primrec.natPair.comp₂ z <| Primrec.natPair.comp₂ y i) :)
  · exact
      have L := (Primrec.fst.comp Primrec.fst).comp Primrec.fst
      have k := k.comp Primrec.fst
      have n := Primrec.unpair.comp (n.comp Primrec.fst)
      have cf := Primrec.fst.comp Primrec.snd
      have z := Primrec.fst.comp n
      have m := Primrec.snd.comp n
      have h₁ := hlup.comp <| L.pair <| (k.pair cf).pair (Primrec.natPair.comp₂ z m)
      Primrec.option_bind h₁ <|
      have m := m.comp Primrec.fst
      Primrec.nat_casesOn Primrec.snd (Primrec.option_some.comp m) <|
      have := hlup.comp <| (L.comp Primrec.fst).pair <|
        ((k'.pair c).comp <| Primrec.fst.comp Primrec.fst).pair <|
        Primrec.natPair.comp₂ (z.comp Primrec.fst) (_root_.Primrec.succ.comp m)
      (this.comp _root_.Primrec.fst).to₂

private theorem evaln_map (k c n) :
    ((((List.range k).get? n).map (evaln k c)).bind fun b => b) = evaln k c n := by
  if kn : n < k then simp [List.get?_range kn] else
  rw [List.get?_len_le]
  · cases e : evaln k c n <;> [rfl; exact kn.elim (evaln_bound e)]
  · simpa using kn

/-- The `Nat.Partrec.Code.evaln` function is primitive recursive. -/
theorem evaln_prim : Primrec fun a : (ℕ × Code) × ℕ => evaln a.1.1 a.1.2 a.2 := by
  suffices Primrec₂ fun (_ : Unit) (n : ℕ) =>
      let a := ofNat (ℕ × Code) n
      (List.range a.1).map (evaln a.1 a.2) from
    (Primrec.option_bind
      (Primrec.list_get?.comp₂ (this.comp₂ (_root_.Primrec.const ())
        (Primrec.encode_iff.2 Primrec.fst)) Primrec.snd) Primrec.snd.to₂).of_eq
      fun ⟨⟨k, c⟩, n⟩ => by simp [evaln_map]
  refine Primrec.nat_strong_rec _ (hG.comp Primrec.snd).to₂ fun _ p => ?_
  simp only [G, prod_ofNat_val, ofNat_nat, List.length_map, List.length_range,
    Nat.pair_unpair, Option.some_inj]
  refine List.map_congr fun n => ?_
  have : List.range p = List.range (Nat.pair p.unpair.1 (encode (ofNat Code p.unpair.2))) := by
    simp
  rw [this]
  generalize ofNat Code p.unpair.2 = c
  match p.unpair.1 with | 0 => simp [evaln] | k' + 1 => ?_
  set k := k' + 1
  intro nk
  simp only [List.mem_range, Nat.lt_succ_iff] at nk
  have hg {k' c' n}
      (hl : Nat.pair k' (encode c') < Nat.pair k (encode c)) :
      lup ((List.range (Nat.pair k (encode c))).map fun n =>
        (List.range n.unpair.1).map (evaln n.unpair.1 (ofNat Code n.unpair.2))) (k', c') n =
        evaln k' c' n := by
    simp [lup, List.get?_range hl, evaln_map, Bind.bind]
  cases c with
    simp only [bind, pure, evaln, nk, guard_true, unpaired, pair_unpair, Option.some_bind]
  | pair cf cg =>
    let ⟨lf, lg⟩ := encode_lt_pair cf cg
    rw [hg (Nat.pair_lt_pair_right _ lf), hg (Nat.pair_lt_pair_right _ lg)]
    cases evaln k cf n <;> [rfl; cases evaln k cg n <;> rfl]
  | comp cf cg =>
    let ⟨lf, lg⟩ := encode_lt_comp cf cg
    rw [hg (Nat.pair_lt_pair_right _ lg)]
    cases evaln k cg n <;> [rfl; simp [hg (Nat.pair_lt_pair_right _ lf)]]
  | prec cf cg =>
    let ⟨lf, lg⟩ := encode_lt_prec cf cg
    rw [hg (Nat.pair_lt_pair_right _ lf)]
    cases n.unpair.2 <;> [rfl; simp only [decode_eq_ofNat, Option.some.injEq]]
    rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
    cases evaln k' _ _ <;> [rfl; simp [hg (Nat.pair_lt_pair_right _ lg)]]
  | rfind' cf =>
    have lf := encode_lt_rfind' cf
    rw [hg (Nat.pair_lt_pair_right _ lf)]
    cases' evaln k cf n with x <;> [rfl; skip]
    simp only [decode_eq_ofNat, Option.some.injEq, Option.some_bind]
    cases x <;> simp only [rec_zero, reduceIte]
    rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
#align nat.partrec.code.evaln_prim Nat.Partrec.Code.evaln_prim

end

section

open Partrec Computable

theorem eval_eq_rfindOpt (c n) : eval c n = Nat.rfindOpt fun k => evaln k c n :=
  Part.ext fun x => by
    refine evaln_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl; apply evaln_mono hl
#align nat.partrec.code.eval_eq_rfind_opt Nat.Partrec.Code.eval_eq_rfindOpt

theorem eval_part : Partrec₂ eval :=
  (Partrec.rfindOpt
    (evaln_prim.to_comp.comp ((Computable.snd.pair (fst.comp fst)).pair (snd.comp fst))).to₂).of_eq
    fun a => by simp [eval_eq_rfindOpt]
#align nat.partrec.code.eval_part Nat.Partrec.Code.eval_part

/-- Roger's fixed-point theorem: Any total, computable `f` has a fixed point: That is, under the
interpretation given by `Nat.Partrec.Code.eval`, there is a code `c` such that `c` and `f c` have
the same evaluation.
-/
theorem fixed_point {f : Code → Code} (hf : Computable f) : ∃ c : Code, eval (f c) = eval c :=
  let g (x y : ℕ) : Part ℕ := eval (ofNat Code x) x >>= fun b => eval (ofNat Code b) y
  have : Partrec₂ g :=
    (eval_part.comp₂ ((Computable.ofNat _).comp fst) fst).bind
      (eval_part.comp₂ ((Computable.ofNat _).comp snd) (snd.comp fst)).to₂
  let ⟨cg, eg⟩ := exists_code.1 this
  have eg' : ∀ a n, eval cg (Nat.pair a n) = Part.map encode (g a n) := by simp [eg]
  let F (x : ℕ) : Code := f (curry cg x)
  have : Computable F :=
    hf.comp (curry_prim.comp₂ (_root_.Primrec.const cg) _root_.Primrec.id).to_comp
  let ⟨cF, eF⟩ := exists_code.1 this
  have eF' : eval cF (encode cF) = Part.some (encode (F (encode cF))) := by simp [eF]
  ⟨curry cg (encode cF),
    funext fun n =>
      show eval (f (curry cg (encode cF))) n = eval (curry cg (encode cF)) n by
        simp [g, eg', eF', Part.map_id']⟩
#align nat.partrec.code.fixed_point Nat.Partrec.Code.fixed_point

theorem fixed_point₂ {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) : ∃ c : Code, eval c = f c :=
  let ⟨cf, ef⟩ := exists_code.1 hf
  (fixed_point (curry_prim.comp₂ (_root_.Primrec.const cf) Primrec.encode).to_comp).imp fun c e =>
    funext fun n => by simp [e.symm, ef, Part.map_id']
#align nat.partrec.code.fixed_point₂ Nat.Partrec.Code.fixed_point₂

end

end Nat.Partrec.Code
