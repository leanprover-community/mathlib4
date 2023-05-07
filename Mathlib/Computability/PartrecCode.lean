/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module computability.partrec_code
! leanprover-community/mathlib commit 6155d4351090a6fad236e3d2e4e0e4e7342668e8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Computability.Partrec

/-!
# Gödel Numbering for Partial Recursive Functions.

This file defines `nat.partrec.code`, an inductive datatype describing code for partial
recursive functions on ℕ. It defines an encoding for these codes, and proves that the constructors
are primitive recursive with respect to the encoding.

It also defines the evalution of these codes as partial functions using `pfun`, and proves that a
function is partially recursive (as defined by `nat.partrec`) if and only if it is the evaluation
of some code.

## Main Definitions

* `nat.partrec.code`: Inductive datatype for partial recursive codes.
* `nat.partrec.code.encode_code`: A (computable) encoding of codes as natural numbers.
* `nat.partrec.code.of_nat_code`: The inverse of this encoding.
* `nat.partrec.code.eval`: The interpretation of a `nat.partrec.code` as a partial function.

## Main Results

* `nat.partrec.code.rec_prim`: Recursion on `nat.partrec.code` is primitive recursive.
* `nat.partrec.code.rec_computable`: Recursion on `nat.partrec.code` is computable.
* `nat.partrec.code.smn`: The $S_n^m$ theorem.
* `nat.partrec.code.exists_code`: Partial recursiveness is equivalent to being the eval of a code.
* `nat.partrec.code.evaln_prim`: `evaln` is primitive recursive.
* `nat.partrec.code.fixed_point`: Roger's fixed point theorem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]

-/


open Encodable Denumerable

namespace Nat.Partrec

open Nat (pair)

theorem rfind' {f} (hf : Nat.Partrec f) :
    Nat.Partrec
      (Nat.unpaired fun a m =>
        (Nat.rfind fun n => (fun m => m = 0) <$> f (pair a (n + m))).map (· + m)) :=
  Partrec₂.unpaired'.2 <|
    by
    refine'
      Partrec.map
        ((@Partrec₂.unpaired' fun a b : ℕ =>
              Nat.rfind fun n => (fun m => m = 0) <$> f (mkpair a (n + b))).1
          _)
        (primrec.nat_add.comp Primrec.snd <| primrec.snd.comp Primrec.fst).to_comp.to₂
    have :=
      rfind
        (Partrec₂.unpaired'.2
          ((Partrec.nat_iff.2 hf).comp
              (primrec₂.mkpair.comp (primrec.fst.comp <| primrec.unpair.comp Primrec.fst)
                  (primrec.nat_add.comp Primrec.snd
                    (primrec.snd.comp <| primrec.unpair.comp Primrec.fst))).to_comp).to₂)
    simp at this; exact this
#align nat.partrec.rfind' Nat.Partrec.rfind'

/-- Code for partial recursive functions from ℕ to ℕ.
See `nat.partrec.code.eval` for the interpretation of these constructors.
-/
inductive Code : Type
  | zero : code
  | succ : code
  | left : code
  | right : code
  | pair : code → code → code
  | comp : code → code → code
  | prec : code → code → code
  | rfind' : code → code
#align nat.partrec.code Nat.Partrec.Code

end Nat.Partrec

namespace Nat.Partrec.Code

open Nat (pair unpair)

open Nat.Partrec (code)

instance : Inhabited Code :=
  ⟨zero⟩

/-- Returns a code for the constant function outputting a particular natural. -/
protected def const : ℕ → Code
  | 0 => zero
  | n + 1 => comp succ (const n)
#align nat.partrec.code.const Nat.Partrec.Code.const

theorem const_inj : ∀ {n₁ n₂}, Nat.Partrec.Code.const n₁ = Nat.Partrec.Code.const n₂ → n₁ = n₂
  | 0, 0, h => by simp
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

/-- An encoding of a `nat.partrec.code` as a ℕ. -/
def encodeCode : Code → ℕ
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | pair cf cg => bit0 (bit0 <| pair (encode_code cf) (encode_code cg)) + 4
  | comp cf cg => bit0 (bit1 <| pair (encode_code cf) (encode_code cg)) + 4
  | prec cf cg => bit1 (bit0 <| pair (encode_code cf) (encode_code cg)) + 4
  | rfind' cf => bit1 (bit1 <| encode_code cf) + 4
#align nat.partrec.code.encode_code Nat.Partrec.Code.encodeCode

/--
A decoder for `nat.partrec.code.encode_code`, taking any ℕ to the `nat.partrec.code` it represents.
-/
def ofNatCode : ℕ → Code
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | n + 4 =>
    let m := n.div2.div2
    have hm : m < n + 4 := by
      simp [m, Nat.div2_val] <;>
        exact
          lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
            (Nat.succ_le_succ (Nat.le_add_right _ _))
    have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | ff, ff => pair (of_nat_code m.unpair.1) (of_nat_code m.unpair.2)
    | ff, tt => comp (of_nat_code m.unpair.1) (of_nat_code m.unpair.2)
    | tt, ff => prec (of_nat_code m.unpair.1) (of_nat_code m.unpair.2)
    | tt, tt => rfind' (of_nat_code m)
#align nat.partrec.code.of_nat_code Nat.Partrec.Code.ofNatCode

/-- Proof that `nat.partrec.code.of_nat_code` is the inverse of `nat.partrec.code.encode_code`-/
private theorem encode_of_nat_code : ∀ n, encodeCode (ofNatCode n) = n
  | 0 => by simp [of_nat_code, encode_code]
  | 1 => by simp [of_nat_code, encode_code]
  | 2 => by simp [of_nat_code, encode_code]
  | 3 => by simp [of_nat_code, encode_code]
  | n + 4 => by
    let m := n.div2.div2
    have hm : m < n + 4 := by
      simp [m, Nat.div2_val] <;>
        exact
          lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
            (Nat.succ_le_succ (Nat.le_add_right _ _))
    have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
    have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode_of_nat_code m
    have IH1 := encode_of_nat_code m.unpair.1
    have IH2 := encode_of_nat_code m.unpair.2
    trans
    swap
    rw [← Nat.bit_decomp n, ← Nat.bit_decomp n.div2]
    simp [encode_code, of_nat_code, -add_comm]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [encode_code, of_nat_code, -add_comm, IH, IH1, IH2, m, Nat.bit]
#align nat.partrec.code.encode_of_nat_code nat.partrec.code.encode_of_nat_code

instance : Denumerable Code :=
  mk'
    ⟨encodeCode, ofNatCode, fun c => by
      induction c <;> try rfl <;> simp [encode_code, of_nat_code, -add_comm, *], encode_ofNatCode⟩

theorem encodeCode_eq : encode = encodeCode :=
  rfl
#align nat.partrec.code.encode_code_eq Nat.Partrec.Code.encodeCode_eq

theorem ofNatCode_eq : ofNat Code = ofNatCode :=
  rfl
#align nat.partrec.code.of_nat_code_eq Nat.Partrec.Code.ofNatCode_eq

theorem encode_lt_pair (cf cg) :
    encode cf < encode (pair cf cg) ∧ encode cg < encode (pair cf cg) :=
  by
  simp [encode_code_eq, encode_code, -add_comm]
  have := Nat.mul_le_mul_right _ (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc, ← bit0_eq_two_mul, ← bit0_eq_two_mul] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 4))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) this, lt_of_le_of_lt (Nat.right_le_pair _ _) this⟩
#align nat.partrec.code.encode_lt_pair Nat.Partrec.Code.encode_lt_pair

theorem encode_lt_comp (cf cg) :
    encode cf < encode (comp cf cg) ∧ encode cg < encode (comp cf cg) :=
  by
  suffices; exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this
  change _; simp [encode_code_eq, encode_code]
#align nat.partrec.code.encode_lt_comp Nat.Partrec.Code.encode_lt_comp

theorem encode_lt_prec (cf cg) :
    encode cf < encode (prec cf cg) ∧ encode cg < encode (prec cf cg) :=
  by
  suffices; exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this
  change _; simp [encode_code_eq, encode_code]
#align nat.partrec.code.encode_lt_prec Nat.Partrec.Code.encode_lt_prec

theorem encode_lt_rfind' (cf) : encode cf < encode (rfind' cf) :=
  by
  simp [encode_code_eq, encode_code, -add_comm]
  have := Nat.mul_le_mul_right _ (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc, ← bit0_eq_two_mul, ← bit0_eq_two_mul] at this
  refine' lt_of_le_of_lt (le_trans this _) (lt_add_of_pos_right _ (by decide : 0 < 4))
  exact le_of_lt (Nat.bit0_lt_bit1 <| le_of_lt <| Nat.bit0_lt_bit1 <| le_rfl)
#align nat.partrec.code.encode_lt_rfind' Nat.Partrec.Code.encode_lt_rfind'

section

open Primrec

theorem pair_prim : Primrec₂ pair :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)
#align nat.partrec.code.pair_prim Nat.Partrec.Code.pair_prim

theorem comp_prim : Primrec₂ comp :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double_succ.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)
#align nat.partrec.code.comp_prim Nat.Partrec.Code.comp_prim

theorem prec_prim : Primrec₂ prec :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 4)
#align nat.partrec.code.prec_prim Nat.Partrec.Code.prec_prim

theorem rfind_prim : Primrec rfind' :=
  ofNat_iff.2 <|
    encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <| nat_double_succ.comp <| encode_iff.2 <| Primrec.ofNat Code)
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
    Primrec (fun a => F a (c a) : α → σ) :=
  by
  intros
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    let a := p.1.1
    let IH := p.1.2
    let n := p.2.1
    let m := p.2.2
    (IH.get? m).bind fun s =>
      (IH.get? m.unpair.1).bind fun s₁ =>
        (IH.get? m.unpair.2).map fun s₂ =>
          cond n.bodd
            (cond n.div2.bodd (rf a (of_nat code m, s))
              (pc a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂)))
            (cond n.div2.bodd (co a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂))
              (pr a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂)))
  have : Primrec G₁ :=
    by
    refine' option_bind (list_nth.comp (snd.comp fst) (snd.comp snd)) _
    refine'
      option_bind
        ((list_nth.comp (snd.comp fst) (fst.comp <| primrec.unpair.comp (snd.comp snd))).comp fst) _
    refine'
      option_map
        ((list_nth.comp (snd.comp fst) (snd.comp <| primrec.unpair.comp (snd.comp snd))).comp <|
          fst.comp fst)
        _
    have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
    have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m₁ := fst.comp (primrec.unpair.comp m)
    have m₂ := snd.comp (primrec.unpair.comp m)
    have s := snd.comp (fst.comp fst)
    have s₁ := snd.comp fst
    have s₂ := snd
    exact
      (nat_bodd.comp n).cond
        ((nat_bodd.comp <| nat_div2.comp n).cond (hrf.comp a (((Primrec.ofNat code).comp m).pair s))
          (hpc.comp a
            (((Primrec.ofNat code).comp m₁).pair <|
              ((Primrec.ofNat code).comp m₂).pair <| s₁.pair s₂)))
        (Primrec.cond (nat_bodd.comp <| nat_div2.comp n)
          (hco.comp a
            (((Primrec.ofNat code).comp m₁).pair <|
              ((Primrec.ofNat code).comp m₂).pair <| s₁.pair s₂))
          (hpr.comp a
            (((Primrec.ofNat code).comp m₁).pair <|
              ((Primrec.ofNat code).comp m₂).pair <| s₁.pair s₂)))
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.cases (some (z a)) fun n =>
      n.cases (some (s a)) fun n =>
        n.cases (some (l a)) fun n => n.cases (some (r a)) fun n => G₁ ((a, IH), n, n.div2.div2)
  have : Primrec₂ G :=
    nat_cases (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <|
      nat_cases snd (option_some_iff.2 (hs.comp (fst.comp fst))) <|
        nat_cases snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <|
          nat_cases snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst)))
            (this.comp <|
              ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
                snd.pair <| nat_div2.comp <| nat_div2.comp snd)
  refine'
    ((nat_strong_rec (fun a n => F a (of_nat code n)) this.to₂ fun a n => _).comp Primrec.id <|
          encode_iff.2 hc).of_eq
      fun a => by simp
  simp
  iterate 4 cases' n with n; · simp [of_nat_code_eq, of_nat_code] <;> rfl
  simp [G]
  rw [List.length_map, List.length_range]
  let m := n.div2.div2
  show
    G₁ ((a, (List.range (n + 4)).map fun n => F a (of_nat code n)), n, m) =
      some (F a (of_nat code (n + 4)))
  have hm : m < n + 4 := by
    simp [Nat.div2_val, m] <;>
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
  have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
  simp [G₁]
  simp [List.get?_map, List.get?_range, hm, m1, m2]
  change of_nat code (n + 4) with of_nat_code (n + 4)
  simp [of_nat_code]
  cases n.bodd <;> cases n.div2.bodd <;> rfl
#align nat.partrec.code.rec_prim' Nat.Partrec.Code.rec_prim'

/-- Recursion on `nat.partrec.code` is primitive recursive. -/
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
  by
  intros
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    let a := p.1.1
    let IH := p.1.2
    let n := p.2.1
    let m := p.2.2
    (IH.get? m).bind fun s =>
      (IH.get? m.unpair.1).bind fun s₁ =>
        (IH.get? m.unpair.2).map fun s₂ =>
          cond n.bodd
            (cond n.div2.bodd (rf a (of_nat code m) s)
              (pc a (of_nat code m.unpair.1) (of_nat code m.unpair.2) s₁ s₂))
            (cond n.div2.bodd (co a (of_nat code m.unpair.1) (of_nat code m.unpair.2) s₁ s₂)
              (pr a (of_nat code m.unpair.1) (of_nat code m.unpair.2) s₁ s₂))
  have : Primrec G₁ :=
    by
    refine' option_bind (list_nth.comp (snd.comp fst) (snd.comp snd)) _
    refine'
      option_bind
        ((list_nth.comp (snd.comp fst) (fst.comp <| primrec.unpair.comp (snd.comp snd))).comp fst) _
    refine'
      option_map
        ((list_nth.comp (snd.comp fst) (snd.comp <| primrec.unpair.comp (snd.comp snd))).comp <|
          fst.comp fst)
        _
    have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
    have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m₁ := fst.comp (primrec.unpair.comp m)
    have m₂ := snd.comp (primrec.unpair.comp m)
    have s := snd.comp (fst.comp fst)
    have s₁ := snd.comp fst
    have s₂ := snd
    exact
      (nat_bodd.comp n).cond
        ((nat_bodd.comp <| nat_div2.comp n).cond
          (hrf.comp <| a.pair (((Primrec.ofNat code).comp m).pair s))
          (hpc.comp <|
            a.pair
              (((Primrec.ofNat code).comp m₁).pair <|
                ((Primrec.ofNat code).comp m₂).pair <| s₁.pair s₂)))
        (Primrec.cond (nat_bodd.comp <| nat_div2.comp n)
          (hco.comp <|
            a.pair
              (((Primrec.ofNat code).comp m₁).pair <|
                ((Primrec.ofNat code).comp m₂).pair <| s₁.pair s₂))
          (hpr.comp <|
            a.pair
              (((Primrec.ofNat code).comp m₁).pair <|
                ((Primrec.ofNat code).comp m₂).pair <| s₁.pair s₂)))
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.cases (some (z a)) fun n =>
      n.cases (some (s a)) fun n =>
        n.cases (some (l a)) fun n => n.cases (some (r a)) fun n => G₁ ((a, IH), n, n.div2.div2)
  have : Primrec₂ G :=
    nat_cases (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <|
      nat_cases snd (option_some_iff.2 (hs.comp (fst.comp fst))) <|
        nat_cases snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <|
          nat_cases snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst)))
            (this.comp <|
              ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
                snd.pair <| nat_div2.comp <| nat_div2.comp snd)
  refine'
    ((nat_strong_rec (fun a n => F a (of_nat code n)) this.to₂ fun a n => _).comp Primrec.id <|
          encode_iff.2 hc).of_eq
      fun a => by simp
  simp
  iterate 4 cases' n with n; · simp [of_nat_code_eq, of_nat_code] <;> rfl
  simp [G]
  rw [List.length_map, List.length_range]
  let m := n.div2.div2
  show
    G₁ ((a, (List.range (n + 4)).map fun n => F a (of_nat code n)), n, m) =
      some (F a (of_nat code (n + 4)))
  have hm : m < n + 4 := by
    simp [Nat.div2_val, m] <;>
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
  have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
  simp [G₁]
  simp [List.get?_map, List.get?_range, hm, m1, m2]
  change of_nat code (n + 4) with of_nat_code (n + 4)
  simp [of_nat_code]
  cases n.bodd <;> cases n.div2.bodd <;> rfl
#align nat.partrec.code.rec_prim Nat.Partrec.Code.rec_prim

end

section

open Computable

/-- Recursion on `nat.partrec.code` is computable. -/
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
    Computable fun a => F a (c a) :=
  by
  -- TODO(Mario): less copy-paste from previous proof
  intros
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    let a := p.1.1
    let IH := p.1.2
    let n := p.2.1
    let m := p.2.2
    (IH.get? m).bind fun s =>
      (IH.get? m.unpair.1).bind fun s₁ =>
        (IH.get? m.unpair.2).map fun s₂ =>
          cond n.bodd
            (cond n.div2.bodd (rf a (of_nat code m, s))
              (pc a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂)))
            (cond n.div2.bodd (co a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂))
              (pr a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂)))
  have : Computable G₁ :=
    by
    refine' option_bind (list_nth.comp (snd.comp fst) (snd.comp snd)) _
    refine'
      option_bind
        ((list_nth.comp (snd.comp fst) (fst.comp <| computable.unpair.comp (snd.comp snd))).comp
          fst)
        _
    refine'
      option_map
        ((list_nth.comp (snd.comp fst) (snd.comp <| computable.unpair.comp (snd.comp snd))).comp <|
          fst.comp fst)
        _
    have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
    have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m₁ := fst.comp (computable.unpair.comp m)
    have m₂ := snd.comp (computable.unpair.comp m)
    have s := snd.comp (fst.comp fst)
    have s₁ := snd.comp fst
    have s₂ := snd
    exact
      (nat_bodd.comp n).cond
        ((nat_bodd.comp <| nat_div2.comp n).cond
          (hrf.comp a (((Computable.ofNat code).comp m).pair s))
          (hpc.comp a
            (((Computable.ofNat code).comp m₁).pair <|
              ((Computable.ofNat code).comp m₂).pair <| s₁.pair s₂)))
        (Computable.cond (nat_bodd.comp <| nat_div2.comp n)
          (hco.comp a
            (((Computable.ofNat code).comp m₁).pair <|
              ((Computable.ofNat code).comp m₂).pair <| s₁.pair s₂))
          (hpr.comp a
            (((Computable.ofNat code).comp m₁).pair <|
              ((Computable.ofNat code).comp m₂).pair <| s₁.pair s₂)))
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.cases (some (z a)) fun n =>
      n.cases (some (s a)) fun n =>
        n.cases (some (l a)) fun n => n.cases (some (r a)) fun n => G₁ ((a, IH), n, n.div2.div2)
  have : Computable₂ G :=
    nat_cases (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <|
      nat_cases snd (option_some_iff.2 (hs.comp (fst.comp fst))) <|
        nat_cases snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <|
          nat_cases snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst)))
            (this.comp <|
              ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
                snd.pair <| nat_div2.comp <| nat_div2.comp snd)
  refine'
    ((nat_strong_rec (fun a n => F a (of_nat code n)) this.to₂ fun a n => _).comp Computable.id <|
          encode_iff.2 hc).of_eq
      fun a => by simp
  simp
  iterate 4 cases' n with n; · simp [of_nat_code_eq, of_nat_code] <;> rfl
  simp [G]
  rw [List.length_map, List.length_range]
  let m := n.div2.div2
  show
    G₁ ((a, (List.range (n + 4)).map fun n => F a (of_nat code n)), n, m) =
      some (F a (of_nat code (n + 4)))
  have hm : m < n + 4 := by
    simp [Nat.div2_val, m] <;>
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
  have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
  simp [G₁]
  simp [List.get?_map, List.get?_range, hm, m1, m2]
  change of_nat code (n + 4) with of_nat_code (n + 4)
  simp [of_nat_code]
  cases n.bodd <;> cases n.div2.bodd <;> rfl
#align nat.partrec.code.rec_computable Nat.Partrec.Code.rec_computable

end

/-- The interpretation of a `nat.partrec.code` as a partial function.
* `nat.partrec.code.zero`: The constant zero function.
* `nat.partrec.code.succ`: The successor function.
* `nat.partrec.code.left`: Left unpairing of a pair of ℕ (encoded by `nat.mkpair`)
* `nat.partrec.code.right`: Right unpairing of a pair of ℕ (encoded by `nat.mkpair`)
* `nat.partrec.code.pair`: Pairs the outputs of argument codes using `nat.mkpair`.
* `nat.partrec.code.comp`: Composition of two argument codes.
* `nat.partrec.code.prec`: Primitive recursion. Given an argument of the form `nat.mkpair a n`:
  * If `n = 0`, returns `eval cf a`.
  * If `n = succ k`, returns `eval cg (mkpair a (mkpair k (eval (prec cf cg) (mkpair a k))))`
* `nat.partrec.code.rfind'`: Minimization. For `f` an argument of the form `nat.mkpair a m`,
  `rfind' f m` returns the least `a` such that `f a m = 0`, if one exists and `f b m` terminates
  for `b < a`
-/
def eval : Code → ℕ →. ℕ
  | zero => pure 0
  | succ => Nat.succ
  | left => ↑fun n : ℕ => n.unpair.1
  | right => ↑fun n : ℕ => n.unpair.2
  | pair cf cg => fun n => pair <$> eval cf n <*> eval cg n
  | comp cf cg => fun n => eval cg n >>= eval cf
  | prec cf cg =>
    Nat.unpaired fun a n =>
      n.elim (eval cf a) fun y IH => do
        let i ← IH
        eval cg (mkpair a (mkpair y i))
  | rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> eval cf (pair a (n + m))).map (· + m)
#align nat.partrec.code.eval Nat.Partrec.Code.eval

/-- Helper lemma for the evaluation of `prec` in the base case. -/
@[simp]
theorem eval_prec_zero (cf cg : Code) (a : ℕ) : eval (prec cf cg) (pair a 0) = eval cf a := by
  rw [eval, Nat.unpaired, Nat.unpair_pair, Nat.rec_zero]
#align nat.partrec.code.eval_prec_zero Nat.Partrec.Code.eval_prec_zero

/-- Helper lemma for the evaluation of `prec` in the recursive case. -/
theorem eval_prec_succ (cf cg : Code) (a k : ℕ) :
    eval (prec cf cg) (pair a (Nat.succ k)) = do
      let ih ← eval (prec cf cg) (pair a k)
      eval cg (mkpair a (mkpair k ih)) :=
  by
  rw [eval, Nat.unpaired, Part.bind_eq_bind, Nat.unpair_pair, Nat.rec_add_one]
  simp
#align nat.partrec.code.eval_prec_succ Nat.Partrec.Code.eval_prec_succ

instance : Membership (ℕ →. ℕ) Code :=
  ⟨fun f c => eval c = f⟩

@[simp]
theorem eval_const : ∀ n m, eval (Code.const n) m = Part.some n
  | 0, m => rfl
  | n + 1, m => by simp! [*]
#align nat.partrec.code.eval_const Nat.Partrec.Code.eval_const

@[simp]
theorem eval_id (n) : eval Code.id n = Part.some n := by simp! [(· <*> ·)]
#align nat.partrec.code.eval_id Nat.Partrec.Code.eval_id

@[simp]
theorem eval_curry (c n x) : eval (curry c n) x = eval c (pair n x) := by simp! [(· <*> ·)]
#align nat.partrec.code.eval_curry Nat.Partrec.Code.eval_curry

theorem const_prim : Primrec Code.const :=
  (Primrec.id.nat_iterate (Primrec.const zero)
        (comp_prim.comp (Primrec.const succ) Primrec.snd).to₂).of_eq
    fun n => by simp <;> induction n <;> simp [*, code.const, Function.iterate_succ']
#align nat.partrec.code.const_prim Nat.Partrec.Code.const_prim

theorem curry_prim : Primrec₂ curry :=
  comp_prim.comp Primrec.fst <| pair_prim.comp (const_prim.comp Primrec.snd) (Primrec.const Code.id)
#align nat.partrec.code.curry_prim Nat.Partrec.Code.curry_prim

theorem curry_inj {c₁ c₂ n₁ n₂} (h : curry c₁ n₁ = curry c₂ n₂) : c₁ = c₂ ∧ n₁ = n₂ :=
  ⟨by injection h, by
    injection h
    injection h with h₁ h₂
    injection h₂ with h₃ h₄
    exact const_inj h₃⟩
#align nat.partrec.code.curry_inj Nat.Partrec.Code.curry_inj

/--
The $S_n^m$ theorem: There is a computable function, namely `nat.partrec.code.curry`, that takes a
program and a ℕ `n`, and returns a new program using `n` as the first argument.
-/
theorem smn : ∃ f : Code → ℕ → Code, Computable₂ f ∧ ∀ c n x, eval (f c n) x = eval c (pair n x) :=
  ⟨curry, Primrec₂.to_comp curry_prim, eval_curry⟩
#align nat.partrec.code.smn Nat.Partrec.Code.smn

/-- A function is partial recursive if and only if there is a code implementing it. -/
theorem exists_code {f : ℕ →. ℕ} : Nat.Partrec f ↔ ∃ c : Code, eval c = f :=
  ⟨fun h => by
    induction h
    case zero => exact ⟨zero, rfl⟩
    case succ => exact ⟨succ, rfl⟩
    case left => exact ⟨left, rfl⟩
    case right => exact ⟨right, rfl⟩
    case pair f g pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨pair cf cg, rfl⟩
    case comp f g pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨comp cf cg, rfl⟩
    case prec f g pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨prec cf cg, rfl⟩
    case rfind f pf hf =>
      rcases hf with ⟨cf, rfl⟩
      refine' ⟨comp (rfind' cf) (pair code.id zero), _⟩
      simp [eval, (· <*> ·), pure, PFun.pure, Part.map_id'],
    fun h => by
    rcases h with ⟨c, rfl⟩; induction c
    case zero => exact Nat.Partrec.zero
    case succ => exact Nat.Partrec.succ
    case left => exact Nat.Partrec.left
    case right => exact Nat.Partrec.right
    case pair cf cg pf pg => exact pf.pair pg
    case comp cf cg pf pg => exact pf.comp pg
    case prec cf cg pf pg => exact pf.prec pg
    case rfind' cf pf => exact pf.rfind'⟩
#align nat.partrec.code.exists_code Nat.Partrec.Code.exists_code

/-- A modified evaluation for the code which returns an `option ℕ` instead of a `part ℕ`. To avoid
undecidability, `evaln` takes a parameter `k` and fails if it encounters a number ≥ k in the course
of its execution. Other than this, the semantics are the same as in `nat.partrec.code.eval`.
-/
def evaln : ∀ k : ℕ, Code → ℕ → Option ℕ
  | 0, _ => fun m => none
  | k + 1, zero => fun n => guard (n ≤ k) >> pure 0
  | k + 1, succ => fun n => guard (n ≤ k) >> pure (Nat.succ n)
  | k + 1, left => fun n => guard (n ≤ k) >> pure n.unpair.1
  | k + 1, right => fun n => guard (n ≤ k) >> pure n.unpair.2
  | k + 1, pair cf cg => fun n =>
    guard (n ≤ k) >> pair <$> evaln (k + 1) cf n <*> evaln (k + 1) cg n
  | k + 1, comp cf cg => fun n =>
    guard (n ≤ k) >> do
      let x ← evaln (k + 1) cg n
      evaln (k + 1) cf x
  | k + 1, prec cf cg => fun n =>
    guard (n ≤ k) >>
      n.unpaired fun a n =>
        n.cases (evaln (k + 1) cf a) fun y => do
          let i ← evaln k (prec cf cg) (pair a y)
          evaln (k + 1) cg (mkpair a (mkpair y i))
  | k + 1, rfind' cf => fun n =>
    guard (n ≤ k) >>
      n.unpaired fun a m => do
        let x ← evaln (k + 1) cf (pair a m)
        if x = 0 then pure m else evaln k (rfind' cf) (mkpair a (m + 1))
#align nat.partrec.code.evaln Nat.Partrec.Code.evaln

theorem evaln_bound : ∀ {k c n x}, x ∈ evaln k c n → n < k
  | 0, c, n, x, h => by simp [evaln] at h <;> cases h
  | k + 1, c, n, x, h =>
    by
    suffices ∀ {o : Option ℕ}, x ∈ guard (n ≤ k) >> o → n < k + 1 by
      cases c <;> rw [evaln] at h <;> exact this h
    simpa [(· >> ·)] using Nat.lt_succ_of_le
#align nat.partrec.code.evaln_bound Nat.Partrec.Code.evaln_bound

theorem evaln_mono : ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ → x ∈ evaln k₁ c n → x ∈ evaln k₂ c n
  | 0, k₂, c, n, x, hl, h => by simp [evaln] at h <;> cases h
  | k + 1, k₂ + 1, c, n, x, hl, h =>
    by
    have hl' := Nat.le_of_succ_le_succ hl
    have :
      ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
        k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) → x ∈ guard (n ≤ k) >> o₁ → x ∈ guard (n ≤ k₂) >> o₂ :=
      by
      simp [(· >> ·)]
      introv h h₁ h₂ h₃
      exact ⟨le_trans h₂ h, h₁ h₃⟩
    simp at h⊢
    induction' c with cf cg hf hg cf cg hf hg cf cg hf hg cf hf generalizing x n <;>
        rw [evaln] at h⊢ <;>
      refine' this hl' (fun h => _) h
    iterate 4 exact h
    · -- pair cf cg
      simp [(· <*> ·)] at h⊢
      exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
    · -- comp cf cg
      simp at h⊢
      exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    · -- prec cf cg
      revert h
      simp
      induction n.unpair.2 <;> simp
      · apply hf
      · exact fun y h₁ h₂ => ⟨y, evaln_mono hl' h₁, hg _ _ h₂⟩
    · -- rfind' cf
      simp at h⊢
      refine' h.imp fun x => And.imp (hf _ _) _
      by_cases x0 : x = 0 <;> simp [x0]
      exact evaln_mono hl'
#align nat.partrec.code.evaln_mono Nat.Partrec.Code.evaln_mono

theorem evaln_sound : ∀ {k c n x}, x ∈ evaln k c n → x ∈ eval c n
  | 0, _, n, x, h => by simp [evaln] at h <;> cases h
  | k + 1, c, n, x, h =>
    by
    induction' c with cf cg hf hg cf cg hf hg cf cg hf hg cf hf generalizing x n <;>
        simp [eval, evaln, (· >> ·), (· <*> ·)] at h⊢ <;>
      cases' h with _ h
    iterate 4 simpa [pure, PFun.pure, eq_comm] using h
    · -- pair cf cg
      rcases h with ⟨y, ef, z, eg, rfl⟩
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    · --comp hf hg
      rcases h with ⟨y, eg, ef⟩
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    · -- prec cf cg
      revert h
      induction' n.unpair.2 with m IH generalizing x <;> simp
      · apply hf
      · refine' fun y h₁ h₂ => ⟨y, IH _ _, _⟩
        · have := evaln_mono k.le_succ h₁
          simp [evaln, (· >> ·)] at this
          exact this.2
        · exact hg _ _ h₂
    · -- rfind' cf
      rcases h with ⟨m, h₁, h₂⟩
      by_cases m0 : m = 0 <;> simp [m0] at h₂
      ·
        exact
          ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun m => (Nat.not_lt_zero _).elim⟩, by
            injection h₂ with h₂ <;> simp [h₂]⟩
      · have := evaln_sound h₂
        simp [eval] at this
        rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
        refine'
          ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun i im => _⟩, by
            simp [add_comm, add_left_comm]⟩
        cases' i with i
        · exact ⟨m, by simpa using hf _ _ h₁, m0⟩
        · rcases hy₂ (Nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩
          exact ⟨z, by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hz, z0⟩
#align nat.partrec.code.evaln_sound Nat.Partrec.Code.evaln_sound

theorem evaln_complete {c n x} : x ∈ eval c n ↔ ∃ k, x ∈ evaln k c n :=
  ⟨fun h => by
    rsuffices ⟨k, h⟩ : ∃ k, x ∈ evaln (k + 1) c n
    · exact ⟨k + 1, h⟩
    induction c generalizing n x <;> simp [eval, evaln, pure, PFun.pure, (· <*> ·), (· >> ·)] at h⊢
    iterate 4 exact ⟨⟨_, le_rfl⟩, h.symm⟩
    case pair cf cg hf hg =>
      rcases h with ⟨x, hx, y, hy, rfl⟩
      rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
      refine' ⟨max k₁ k₂, _⟩
      refine'
        ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
          evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
          evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
    case comp cf cg hf hg =>
      rcases h with ⟨y, hy, hx⟩
      rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx with ⟨k₂, hk₂⟩
      refine' ⟨max k₁ k₂, _⟩
      exact
        ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
          evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
          evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂⟩
    case prec cf cg hf hg =>
      revert h
      generalize n.unpair.1 = n₁; generalize n.unpair.2 = n₂
      induction' n₂ with m IH generalizing x n <;> simp
      · intro
        rcases hf h with ⟨k, hk⟩
        exact ⟨_, le_max_left _ _, evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
      · intro y hy hx
        rcases IH hy with ⟨k₁, nk₁, hk₁⟩
        rcases hg hx with ⟨k₂, hk₂⟩
        refine'
          ⟨(max k₁ k₂).succ,
            Nat.le_succ_of_le <| le_max_of_le_left <| le_trans (le_max_left _ (mkpair n₁ m)) nk₁, y,
            evaln_mono (Nat.succ_le_succ <| le_max_left _ _) _,
            evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_right _ _) hk₂⟩
        simp [evaln, (· >> ·)]
        exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩
    case rfind' cf hf =>
      rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
      suffices ∃ k, y + n.unpair.2 ∈ evaln (k + 1) (rfind' cf) (mkpair n.unpair.1 n.unpair.2) by
        simpa [evaln, (· >> ·)]
      revert hy₁ hy₂
      generalize n.unpair.2 = m
      intros
      induction' y with y IH generalizing m <;> simp [evaln, (· >> ·)]
      · simp at hy₁
        rcases hf hy₁ with ⟨k, hk⟩
        exact ⟨_, Nat.le_of_lt_succ <| evaln_bound hk, _, hk, by simp <;> rfl⟩
      · rcases hy₂ (Nat.succ_pos _) with ⟨a, ha, a0⟩
        rcases hf ha with ⟨k₁, hk₁⟩
        rcases IH m.succ (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
            fun i hi => by
            simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using
              hy₂ (Nat.succ_lt_succ hi) with
          ⟨k₂, hk₂⟩
        use (max k₁ k₂).succ
        rw [zero_add] at hk₁
        use Nat.le_succ_of_le <| le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁
        use a
        use evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
        simpa [Nat.succ_eq_add_one, a0, -max_eq_left, -max_eq_right, add_comm, add_left_comm] using
          evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂,
    fun ⟨k, h⟩ => evaln_sound h⟩
#align nat.partrec.code.evaln_complete Nat.Partrec.Code.evaln_complete

section

open Primrec

private def lup (L : List (List (Option ℕ))) (p : ℕ × Code) (n : ℕ) := do
  let l ← L.get? (encode p)
  let o ← l.get? n
  o
#align nat.partrec.code.lup nat.partrec.code.lup

private theorem hlup : Primrec fun p : _ × (_ × _) × _ => lup p.1 p.2.1 p.2.2 :=
  option_bind (list_get?.comp fst (Primrec.encode.comp <| fst.comp snd))
    (option_bind (list_get?.comp snd <| snd.comp <| snd.comp fst) snd)
#align nat.partrec.code.hlup nat.partrec.code.hlup

private def G (L : List (List (Option ℕ))) : Option (List (Option ℕ)) :=
  Option.some <|
    let a := ofNat (ℕ × Code) L.length
    let k := a.1
    let c := a.2
    (List.range k).map fun n =>
      k.cases none fun k' =>
        Nat.Partrec.Code.recOn c (some 0)
          (-- zero
            some
            (Nat.succ n))
          (some n.unpair.1) (some n.unpair.2)
          (fun cf cg _ _ => do
            let x ← lup L (k, cf) n
            let y ← lup L (k, cg) n
            some (mkpair x y))
          (fun cf cg _ _ => do
            let x ← lup L (k, cg) n
            lup L (k, cf) x)
          (fun cf cg _ _ =>
            let z := n.unpair.1
            n.unpair.2.cases (lup L (k, cf) z) fun y => do
              let i ← lup L (k', c) (pair z y)
              lup L (k, cg) (mkpair z (mkpair y i)))
          fun cf _ =>
          let z := n.unpair.1
          let m := n.unpair.2
          do
          let x ← lup L (k, cf) (pair z m)
          x (some m) fun _ => lup L (k', c) (mkpair z (m + 1))
#align nat.partrec.code.G nat.partrec.code.G

private theorem hG : Primrec g :=
  by
  have a := (Primrec.ofNat (ℕ × code)).comp list_length
  have k := fst.comp a
  refine' option_some.comp (list_map (list_range.comp k) (_ : Primrec _))
  replace k := k.comp fst; have n := snd
  refine' nat_cases k (const none) (_ : Primrec _)
  have k := k.comp fst; have n := n.comp fst; have k' := snd
  have c := snd.comp (a.comp <| fst.comp fst)
  apply
    rec_prim c (const (some 0)) (option_some.comp (primrec.succ.comp n))
      (option_some.comp (fst.comp <| primrec.unpair.comp n))
      (option_some.comp (snd.comp <| primrec.unpair.comp n))
  · have L := (fst.comp fst).comp fst
    have k := k.comp fst
    have n := n.comp fst
    have cf := fst.comp snd
    have cg := (fst.comp snd).comp snd
    exact
      option_bind (hlup.comp <| L.pair <| (k.pair cf).pair n)
        (option_map ((hlup.comp <| L.pair <| (k.pair cg).pair n).comp fst)
          (primrec₂.mkpair.comp (snd.comp fst) snd))
  · have L := (fst.comp fst).comp fst
    have k := k.comp fst
    have n := n.comp fst
    have cf := fst.comp snd
    have cg := (fst.comp snd).comp snd
    exact
      option_bind (hlup.comp <| L.pair <| (k.pair cg).pair n)
        (hlup.comp ((L.comp fst).pair <| ((k.pair cf).comp fst).pair snd))
  · have L := (fst.comp fst).comp fst
    have k := k.comp fst
    have n := n.comp fst
    have cf := fst.comp snd
    have cg := (fst.comp snd).comp snd
    have z := fst.comp (primrec.unpair.comp n)
    refine'
      nat_cases (snd.comp (primrec.unpair.comp n)) (hlup.comp <| L.pair <| (k.pair cf).pair z)
        (_ : Primrec _)
    have L := L.comp fst
    have z := z.comp fst
    have y := snd
    refine'
      option_bind
        (hlup.comp <| L.pair <| (((k'.pair c).comp fst).comp fst).pair (primrec₂.mkpair.comp z y))
        (_ : Primrec _)
    have z := z.comp fst
    have y := y.comp fst
    have i := snd
    exact
      hlup.comp
        ((L.comp fst).pair <|
          ((k.pair cg).comp <| fst.comp fst).pair <|
            primrec₂.mkpair.comp z <| primrec₂.mkpair.comp y i)
  · have L := (fst.comp fst).comp fst
    have k := k.comp fst
    have n := n.comp fst
    have cf := fst.comp snd
    have z := fst.comp (primrec.unpair.comp n)
    have m := snd.comp (primrec.unpair.comp n)
    refine'
      option_bind (hlup.comp <| L.pair <| (k.pair cf).pair (primrec₂.mkpair.comp z m))
        (_ : Primrec _)
    have m := m.comp fst
    exact
      nat_cases snd (option_some.comp m)
        ((hlup.comp
              ((L.comp fst).pair <|
                ((k'.pair c).comp <| fst.comp fst).pair
                  (primrec₂.mkpair.comp (z.comp fst) (primrec.succ.comp m)))).comp
          fst)
#align nat.partrec.code.hG nat.partrec.code.hG

private theorem evaln_map (k c n) :
    ((((List.range k).get? n).map (evaln k c)).bind fun b => b) = evaln k c n :=
  by
  by_cases kn : n < k
  · simp [List.get?_range kn]
  · rw [List.get?_len_le]
    · cases e : evaln k c n
      · rfl
      exact kn.elim (evaln_bound e)
    simpa using kn
#align nat.partrec.code.evaln_map nat.partrec.code.evaln_map

/-- The `nat.partrec.code.evaln` function is primitive recursive. -/
theorem evaln_prim : Primrec fun a : (ℕ × Code) × ℕ => evaln a.1.1 a.1.2 a.2 :=
  have :
    Primrec₂ fun (_ : Unit) (n : ℕ) =>
      let a := ofNat (ℕ × Code) n
      (List.range a.1).map (evaln a.1 a.2) :=
    Primrec.nat_strong_rec _ (hG.comp snd).to₂ fun _ p =>
      by
      simp [G]
      rw [(_ : (of_nat (ℕ × code) _).snd = of_nat code p.unpair.2)]
      swap
      · simp
      apply List.map_congr fun n => _
      rw [(by simp :
          List.range p = List.range (mkpair p.unpair.1 (encode (of_nat code p.unpair.2))))]
      generalize p.unpair.1 = k
      generalize of_nat code p.unpair.2 = c
      intro nk
      cases' k with k'
      · simp [evaln]
      let k := k' + 1
      change k'.succ with k
      simp [Nat.lt_succ_iff] at nk
      have hg :
        ∀ {k' c' n},
          mkpair k' (encode c') < mkpair k (encode c) →
            lup
                ((List.range (mkpair k (encode c))).map fun n =>
                  (List.range n.unpair.1).map (evaln n.unpair.1 (of_nat code n.unpair.2)))
                (k', c') n =
              evaln k' c' n :=
        by
        intro k₁ c₁ n₁ hl
        simp [lup, List.get?_range hl, evaln_map, (· >>= ·)]
      cases' c with cf cg cf cg cf cg cf <;>
        simp [evaln, nk, (· >> ·), (· >>= ·), (· <$> ·), (· <*> ·), pure]
      · cases' encode_lt_pair cf cg with lf lg
        rw [hg (Nat.pair_lt_pair_right _ lf), hg (Nat.pair_lt_pair_right _ lg)]
        cases evaln k cf n
        · rfl
        cases evaln k cg n <;> rfl
      · cases' encode_lt_comp cf cg with lf lg
        rw [hg (Nat.pair_lt_pair_right _ lg)]
        cases evaln k cg n
        · rfl
        simp [hg (Nat.pair_lt_pair_right _ lf)]
      · cases' encode_lt_prec cf cg with lf lg
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        cases n.unpair.2
        · rfl
        simp
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
        cases evaln k' _ _
        · rfl
        simp [hg (Nat.pair_lt_pair_right _ lg)]
      · have lf := encode_lt_rfind' cf
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        cases' evaln k cf n with x
        · rfl
        simp
        cases x <;> simp [Nat.succ_ne_zero]
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
  (option_bind (list_get?.comp (this.comp (const ()) (encode_iff.2 fst)) snd) snd.to₂).of_eq
    fun ⟨⟨k, c⟩, n⟩ => by simp [evaln_map]
#align nat.partrec.code.evaln_prim Nat.Partrec.Code.evaln_prim

end

section

open Partrec Computable

theorem eval_eq_rfindOpt (c n) : eval c n = Nat.rfindOpt fun k => evaln k c n :=
  Part.ext fun x => by
    refine' evaln_complete.trans (Nat.rfindOpt_mono _).symm
    intro a m n hl; apply evaln_mono hl
#align nat.partrec.code.eval_eq_rfind_opt Nat.Partrec.Code.eval_eq_rfindOpt

theorem eval_part : Partrec₂ eval :=
  (rfindOpt (evaln_prim.to_comp.comp ((snd.pair (fst.comp fst)).pair (snd.comp fst))).to₂).of_eq
    fun a => by simp [eval_eq_rfind_opt]
#align nat.partrec.code.eval_part Nat.Partrec.Code.eval_part

/-- Roger's fixed-point theorem: Any total, computable `f` has a fixed point: That is, under the
interpretation given by `nat.partrec.code.eval`, there is a code `c` such that `c` and `f c` have
the same evaluation.
-/
theorem fixed_point {f : Code → Code} (hf : Computable f) : ∃ c : Code, eval (f c) = eval c :=
  let g (x y : ℕ) : Part ℕ := eval (ofNat Code x) x >>= fun b => eval (ofNat Code b) y
  have : Partrec₂ g :=
    (eval_part.comp ((Computable.ofNat _).comp fst) fst).bind
      (eval_part.comp ((Computable.ofNat _).comp snd) (snd.comp fst)).to₂
  let ⟨cg, eg⟩ := exists_code.1 this
  have eg' : ∀ a n, eval cg (pair a n) = Part.map encode (g a n) := by simp [eg]
  let F (x : ℕ) : Code := f (curry cg x)
  have : Computable F := hf.comp (curry_prim.comp (Primrec.const cg) Primrec.id).to_comp
  let ⟨cF, eF⟩ := exists_code.1 this
  have eF' : eval cF (encode cF) = Part.some (encode (F (encode cF))) := by simp [eF]
  ⟨curry cg (encode cF),
    funext fun n =>
      show eval (f (curry cg (encode cF))) n = eval (curry cg (encode cF)) n by
        simp [eg', eF', Part.map_id', g]⟩
#align nat.partrec.code.fixed_point Nat.Partrec.Code.fixed_point

theorem fixed_point₂ {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) : ∃ c : Code, eval c = f c :=
  let ⟨cf, ef⟩ := exists_code.1 hf
  (fixed_point (curry_prim.comp (Primrec.const cf) Primrec.encode).to_comp).imp fun c e =>
    funext fun n => by simp [e.symm, ef, Part.map_id']
#align nat.partrec.code.fixed_point₂ Nat.Partrec.Code.fixed_point₂

end

end Nat.Partrec.Code

