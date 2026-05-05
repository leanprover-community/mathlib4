/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Modifications:
Copyright (c) 2026 Edwin Park.
-/
import Mathlib.Computability.SingleOracle.Label
import Mathlib.Computability.SingleOracle.Oracle
import Mathlib.Data.Option.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Cases -- for induction'

/-!
# Gödel Numbering for Functions Partial Recursive in an Oracle.

This file is a relativisation of Mathlib/Computability/PartrecCode.lean; notable notions relativised
include:

- `Oracle.Single.Code`: where a constructor for the oracle is added;
- `Oracle.Single.Code.c2n`: A relativisation of `Nat.Partrec.Code.encodeCode`
- `Oracle.Single.Code.n2c`: A relativisation of `Nat.Partrec.Code.ofNatCode`
- `Oracle.Single.eval` : A relativisation of `Nat.Partrec.Code.eval`

-/

open Nat Encodable Denumerable

namespace Oracle.Single

inductive Code : Type
| zero  : Code
| succ  : Code
| left  : Code
| right : Code
| oracle : Code
| pair  : Code → Code → Code
| comp  : Code → Code → Code
| prec  : Code → Code → Code
| rfind' : Code → Code

compile_inductive% Code
end Oracle.Single
namespace Oracle.Single.Code
instance instInhabited : Inhabited Code := ⟨zero⟩

/-- Returns a code for the constant function outputting a particular natural. -/
protected def const : ℕ → Code
  | 0 => zero
  | n + 1 => comp succ (Code.const n)

theorem const_inj : ∀ {n₁ n₂}, Code.const n₁ = Code.const n₂ → n₁ = n₂
  | 0, 0, _ => by simp
  | n₁ + 1, n₂ + 1, h => by
    dsimp [Code.const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]

/-- A code for the identity function. -/
protected def id : Code :=
  pair left right

/-- Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
def curry (c : Code) (n : ℕ) : Code :=
  comp c (pair (Code.const n) Code.id)

/-- An encoding of a `Oracle.Single.Code` as a ℕ. -/
def c2n : Code → ℕ
| Code.zero        => 0
| Code.succ        => 1
| Code.left        => 2
| Code.right       => 3
| Code.oracle      => 4
| Code.pair cf cg  => 2*(2*(Nat.pair (c2n cf) (c2n cg))  )   + 5
| Code.comp cf cg  => 2*(2*(Nat.pair (c2n cf) (c2n cg))  )+1 + 5
| Code.prec cf cg  => 2*(2*(Nat.pair (c2n cf) (c2n cg))+1)   + 5
| Code.rfind' cf   => 2*(2*(c2n cf                            )+1)+1 + 5

/--
A decoder for `Oracle.Single.Code.c2n`, taking any ℕ to the `Oracle.Single.Code` it represents.

Procedure for decoding:

If `n ≤ 4`. trivial.

Otherwise if `n ≥ 5`, check `n % 4`. The 4 possible values correspond to either
`pair`, `comp`, `prec`, or `rfind'`.
-/
def n2c : ℕ → Code
| 0 => zero
| 1 => succ
| 2 => left
| 3 => right
| 4 => oracle
| n + 5 =>
  let m := n.div2.div2
  have hm : m < n + 5 := by
    simp only [m, Nat.div2_val]
    exact
      lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
        (Nat.succ_le_succ (Nat.le_add_right _ _))
  have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
  have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
  match n.bodd, n.div2.bodd with
  | false, false => pair (n2c m.unpair.1) (n2c m.unpair.2) -- n%4=0
  | true , false => comp (n2c m.unpair.1) (n2c m.unpair.2) -- n%4=1
  | false, true  => prec (n2c m.unpair.1) (n2c m.unpair.2) -- n%4=2
  | true , true  => rfind' (n2c m)                         -- n%4=3

instance {m} : OfNat (Code) m where ofNat := n2c m
instance : Coe ℕ Code := ⟨n2c⟩
instance : Coe Code ℕ := ⟨c2n⟩
-- /-- Converts an `Code` into a `ℕ`. -/ @[coe] def ofCode : Code → ℕ := encodeCode
abbrev ofNatCode := n2c
@[simp] abbrev _root_.Nat.n2c : ℕ → Code := Oracle.Single.Code.n2c

@[simp] theorem n2c_c2n : ∀ c, n2c (c2n c) = c := fun c => by
  induction c <;> (simp [c2n, n2c, Nat.div2_val, *])
@[simp] theorem c2n_n2c : ∀ c, c2n (n2c c) = c :=
fun c => match c with
  | 0 => by simp only [n2c, c2n]
  | 1 => by simp only [n2c, c2n]
  | 2 => by simp only [n2c, c2n]
  | 3 => by simp only [n2c, c2n]
  | 4 => by simp only [n2c, c2n]
  | n + 5 => by
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, Nat.div2_val]
      exact lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
        (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := c2n_n2c m
    have IH1 := c2n_n2c m.unpair.1
    have IH2 := c2n_n2c m.unpair.2
    conv_rhs => rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 n.div2]
    simp only [n2c.eq_6]
    cases n.bodd <;> cases n.div2.bodd <;> simp [m, c2n, IH, IH1, IH2, Nat.bit_val]
instance instDenumerable : Denumerable Code := mk' ⟨c2n, n2c, n2c_c2n, c2n_n2c⟩

theorem n2c_bij : Function.Bijective n2c :=
  Function.bijective_iff_has_inverse.mpr ⟨c2n, ⟨fun x ↦ c2n_n2c x, fun x ↦ n2c_c2n x⟩⟩
theorem n2c_inj : Function.Injective n2c := Function.Bijective.injective n2c_bij
theorem n2c_sur : Function.Surjective n2c := Function.Bijective.surjective n2c_bij
theorem encodeCode_bij : Function.Bijective c2n :=
  Function.bijective_iff_has_inverse.mpr ⟨n2c, ⟨fun x ↦ n2c_c2n x, fun x ↦ c2n_n2c x⟩⟩
theorem encodeCode_inj : Function.Injective c2n := Function.Bijective.injective encodeCode_bij
theorem encodeCode_sur : Function.Surjective c2n := Function.Bijective.surjective encodeCode_bij


/-- Proof that `Oracle.Single.Code.ofNatCode` is the inverse of `Oracle.Single.Code.encodeCode` -/
private theorem encode_ofNatCode : ∀ n, c2n (ofNatCode n) = n := by exact fun n ↦c2n_n2c n

theorem encodeCode_eq : encode = c2n :=
  rfl

theorem ofNatCode_eq : ofNat Code = ofNatCode :=
  rfl

theorem encode_lt_pair (cf cg) :
    encode cf < encode (pair cf cg) ∧ encode cg < encode (pair cf cg) := by
  simp only [encodeCode_eq, c2n]
  have := Nat.mul_le_mul_right (Nat.pair cf.c2n cg.c2n) (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 5))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) this, lt_of_le_of_lt (Nat.right_le_pair _ _) this⟩

theorem encode_lt_comp (cf cg) :
    encode cf < encode (comp cf cg) ∧ encode cg < encode (comp cf cg) := by
  have : encode (pair cf cg) < encode (comp cf cg) := by simp [encodeCode_eq, c2n]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_prec (cf cg) :
    encode cf < encode (prec cf cg) ∧ encode cg < encode (prec cf cg) := by
  have : encode (pair cf cg) < encode (prec cf cg) := by simp [encodeCode_eq, c2n]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_rfind' (cf) : encode cf < encode (rfind' cf) := by
  simp only [encodeCode_eq, c2n]
  omega

end Code

open Code
/-- The interpretation of a `Oracle.Single.Code` as a partial function.
* `Oracle.Single.Code.zero`: The constant zero function.
* `Oracle.Single.Code.succ`: The successor function.
* `Oracle.Single.Code.left`: Left unpairing of a pair of ℕ (encoded by `Nat.pair`)
* `Oracle.Single.Code.right`: Right unpairing of a pair of ℕ (encoded by `Nat.pair`)
* `Oracle.Single.Code.oracle`: The oracle function.
* `Oracle.Single.Code.pair`: Pairs the outputs of argument codes using `Nat.pair`.
* `Oracle.Single.Code.comp`: Composition of two argument codes.
* `Oracle.Single.Code.prec`: Primitive recursion. Given an argument of the form `Nat.pair a n`:
  * If `n = 0`, returns `eval O cf a`.
  * If `n = succ k`, returns `eval O cg (pair a (pair k (eval O (prec cf cg) (pair a k))))`
* `Oracle.Single.Code.rfind'`: Minimization. For `f` an argument of the form `Nat.pair a m`,
  `rfind' f m` returns the least `a` such that `f a m = 0`, if one exists and `f b m` terminates
  for `b < a`
-/
@[ev_simps] def eval (O : ℕ → ℕ) : Code → ℕ →. ℕ
| .zero => fun _ ↦ some 0
| .succ => fun n ↦ some (n + 1)
| .left => fun n ↦ some (Nat.unpair n).1
| .right => fun n ↦ some (Nat.unpair n).2
| .oracle => O
| .pair cf cg => fun n ↦ Nat.pair <$> eval O cf n <*> eval O cg n
| .comp cf cg => fun n ↦ eval O cg n >>= eval O cf
| .prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (eval O cf a) fun y IH => do
        let i ← IH
        eval O cg (Nat.pair a (Nat.pair y i))
| .rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n ↦ (fun x => x = 0) <$> eval O cf (Nat.pair a (n + m))).map (· + m)

/-- Helper lemma for the evaluation of `prec` in the base case. -/
@[simp]
theorem eval_prec_zero {O : ℕ → ℕ} (cf cg : Code) (a : ℕ) :
    eval O (prec cf cg) (Nat.pair a 0) = eval O cf a := by
  rw [eval, Nat.unpaired, Nat.unpair_pair]
  simp (config := { Lean.Meta.Simp.neutralConfig with proj := true }) only []
  rw [Nat.rec_zero]

/-- Helper lemma for the evaluation of `prec` in the recursive case. -/
theorem eval_prec_succ {O : ℕ → ℕ} (cf cg : Code) (a k : ℕ) :
    eval O (prec cf cg) (Nat.pair a (Nat.succ k)) =
      do {let ih ← eval O (prec cf cg) (Nat.pair a k); eval O cg (Nat.pair a (Nat.pair k ih))} := by
  rw [eval, Nat.unpaired, Part.bind_eq_bind, Nat.unpair_pair]
  simp

@[simp]
theorem eval_const {O : ℕ → ℕ} : ∀ n m, eval O (Code.const n) m = Part.some n
  | 0, _ => rfl
  | n + 1, m => by simp! [eval_const n m]

@[simp]
theorem eval_id {O : ℕ → ℕ} (n) : eval O Code.id n = Part.some n := by simp! [Seq.seq, Code.id]

@[simp]
theorem eval_curry {O : ℕ → ℕ} (c n x) : eval O (curry c n) x = eval O c (Nat.pair n x) := by
  simp! [Seq.seq, curry]

/-- A function is partial recursive if and only if there is a code implementing it. Therefore,
`eval` is a **universal partial recursive function**. -/
theorem exists_code {O : ℕ → ℕ} {f : ℕ →. ℕ} : RecursiveIn O f ↔ ∃ c : Code, eval O c = f := by
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | zero => exact ⟨.zero, rfl⟩
    | succ => exact ⟨succ, rfl⟩
    | left => exact ⟨left, rfl⟩
    | right => exact ⟨right, rfl⟩
    | oracle => exact ⟨oracle, rfl⟩
    | pair pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨.pair cf cg, rfl⟩
    | comp pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨comp cf cg, rfl⟩
    | prec pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨prec cf cg, rfl⟩
    | rfind pf hf =>
      rcases hf with ⟨cf, rfl⟩
      use rfind' cf
      exact rfl
  · rintro ⟨c, rfl⟩
    induction c with
    | zero => exact RecursiveIn.zero
    | succ => exact RecursiveIn.succ
    | left => exact RecursiveIn.left
    | right => exact RecursiveIn.right
    | oracle => exact RecursiveIn.oracle
    | pair cf cg pf pg => exact pf.pair pg
    | comp cf cg pf pg => exact pf.comp pg
    | prec cf cg pf pg => exact pf.prec pg
    | rfind' cf pf =>
      simpa [eval] using RecursiveIn.rfind pf

/- A modified evaluation for the code which returns an `Option ℕ` instead of a `Part ℕ`. To avoid
undecidability, `evaln` takes a parameter `k` and fails if it encounters a number ≥ k in the course
of its execution. Other than this, the semantics are the same as in `Oracle.Single.Code.eval`.
-/
def evaln (O : ℕ → ℕ) : ℕ → Code → ℕ → Option ℕ
| 0, _ => fun _ => Option.none
| k + 1, .zero => fun n => do
  guard (n ≤ k)
  return 0
| k + 1, .succ => fun n => do
  guard (n ≤ k)
  return (Nat.succ n)
| k + 1, .left => fun n => do
  guard (n ≤ k)
  return n.unpair.1
| k + 1, .right => fun n => do
  guard (n ≤ k)
  pure n.unpair.2
| k + 1, .oracle => fun n => do
  guard (n ≤ k)
  pure (O n)
| k + 1, .pair cf cg => fun n => do
  guard (n ≤ k)
  Nat.pair <$> evaln O (k + 1) cf n <*> evaln O (k + 1) cg n
| k + 1, .comp cf cg => fun n => do
  guard (n ≤ k)
  let x ← evaln O (k + 1) cg n
  evaln O (k + 1) cf x
| k + 1, .prec cf cg => fun n => do
  guard (n ≤ k)
  n.unpaired fun a n =>
    n.casesOn (evaln O (k + 1) cf a) fun y => do
      let i ← evaln O k (prec cf cg) (Nat.pair a y)
      evaln O (k + 1) cg (Nat.pair a (Nat.pair y i))
| k + 1, .rfind' cf => fun n => do
  guard (n ≤ k)
  n.unpaired fun a m => do
    let x ← evaln O (k + 1) cf (Nat.pair a m)
    if x = 0 then
      pure m
    else
      evaln O k (rfind' cf) (Nat.pair a (m + 1))

theorem evaln_bound {O : ℕ → ℕ} : ∀ {k c n x}, x ∈ evaln O k c n → n < k
  | 0, c, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    suffices ∀ {o : Option ℕ}, x ∈ do { guard (n ≤ k); o } → n < k + 1 by
      cases c <;> rw [evaln] at h <;> exact this h
    simpa [Option.bind_eq_some_iff] using Nat.lt_succ_of_le

set_option linter.flexible false in
theorem evaln_mono {O : ℕ → ℕ} : ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ → x ∈ evaln O k₁ c n → x ∈ evaln O k₂ c n
  | 0, k₂, c, n, x, _, h => by simp [evaln] at h
  | k + 1, k₂ + 1, c, n, x, hl, h => by
    have hl' := Nat.le_of_succ_le_succ hl
    have :
      ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
        k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) →
          x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k₂); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
        exists_and_left, exists_const, and_imp]
      introv h h₁ h₂ h₃
      exact ⟨le_trans h₂ h, h₁ h₃⟩
    simp? at h ⊢ says simp only [Option.mem_def] at h ⊢
    induction c generalizing x n <;> rw [evaln] at h ⊢ <;> refine this hl' (fun h => ?_) h
    iterate 5 exact h
    case pair cf cg hf hg _ =>
      simp? [Seq.seq, Option.bind_eq_some_iff] at h ⊢ says
        simp only [Seq.seq, Option.map_eq_map, Option.mem_def, Option.bind_eq_some_iff,
          Option.map_eq_some_iff, exists_exists_and_eq_and] at h ⊢
      exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
    case comp cf cg hf hg _ =>
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [bind, Option.mem_def, Option.bind_eq_some_iff] at h ⊢
      exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    case prec cf cg hf hg _ =>
      revert h
      simp only [unpaired, bind, Option.mem_def]
      induction n.unpair.2 <;> simp [Option.bind_eq_some_iff]
      · apply hf
      · exact fun y h₁ h₂ => ⟨y, evaln_mono hl' h₁, hg _ _ h₂⟩
    case rfind' cf hf _ =>
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
          Option.bind_eq_some_iff] at h ⊢
      refine h.imp fun x => And.imp (hf _ _) ?_
      by_cases x0 : x = 0 <;> simp [x0]
      exact evaln_mono hl'

set_option linter.flexible false in 
theorem evaln_sound {O : ℕ → ℕ} : ∀ {k c n x}, x ∈ evaln O k c n → x ∈ eval O c n
  | 0, _, n, x, h => by simp [evaln] at h
  | k + 1, c, n, x, h => by
    induction c generalizing x n <;> simp [eval, evaln, Option.bind_eq_some_iff, Seq.seq] at h ⊢ <;>
      obtain ⟨_, h⟩ := h
    iterate 5 simpa [pure, PFun.pure, eq_comm] using h
    case pair cf cg hf hg _ =>
      rcases h with ⟨y, ef, z, eg, rfl⟩
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    case comp cf cg hf hg _ =>
      rcases h with ⟨y, eg, ef⟩
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    case prec cf cg hf hg _ =>
      revert h
      induction n.unpair.2 generalizing x with simp [Option.bind_eq_some_iff]
      | zero => apply hf
      | succ m IH =>
        refine fun y h₁ h₂ => ⟨y, IH _ ?_, ?_⟩
        · have := evaln_mono k.le_succ h₁
          simp [evaln, Option.bind_eq_some_iff] at this
          exact this.2
        · exact hg _ _ h₂
    case rfind' cf hf _ =>
      rcases h with ⟨m, h₁, h₂⟩
      by_cases m0 : m = 0 <;> simp [m0] at h₂
      · exact
          ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun {m} => (Nat.not_lt_zero _).elim⟩, by simp [h₂]⟩
      · have := evaln_sound h₂
        simp [eval] at this
        rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
        refine
          ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun {i} im => ?_⟩, by
            simp [add_comm, add_left_comm]⟩
        rcases i with - | i
        · exact ⟨m, by simpa using hf _ _ h₁, m0⟩
        · rcases hy₂ (Nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩
          exact ⟨z, by simpa [add_comm, add_left_comm] using hz, z0⟩


set_option linter.flexible false in 
theorem evaln_complete {O : ℕ → ℕ} {c n x} : x ∈ eval O c n ↔ ∃ k, x ∈ evaln O k c n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => evaln_sound h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ evaln O (k + 1) c n
  · exact ⟨k + 1, h⟩
  induction c generalizing n x with
      simp [eval, evaln, pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
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
    induction n₂ generalizing x n with simp [Option.bind_eq_some_iff]
    | zero =>
      intro h
      rcases hf h with ⟨k, hk⟩
      exact ⟨_, le_max_left _ _, evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    | succ m IH =>
      intro y hy hx
      rcases IH hy with ⟨k₁, nk₁, hk₁⟩
      rcases hg hx with ⟨k₂, hk₂⟩
      refine
        ⟨(max k₁ k₂).succ,
          Nat.le_succ_of_le <| le_max_of_le_left <|
            le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁, y,
          evaln_mono (Nat.succ_le_succ <| le_max_left _ _) ?_,
          evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_right _ _) hk₂⟩
      simp only [evaln, bind, unpaired, unpair_pair, Option.mem_def, Option.bind_eq_some_iff,
        Option.guard_eq_some', exists_and_left, exists_const]
      exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩
  | rfind' cf hf =>
    rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    suffices ∃ k, y + n.unpair.2 ∈ evaln O (k + 1) (rfind' cf) (Nat.pair n.unpair.1 n.unpair.2) by
      simpa [evaln, Option.bind_eq_some_iff]
    revert hy₁ hy₂
    generalize n.unpair.2 = m
    intro hy₁ hy₂
    induction y generalizing m with simp [evaln, Option.bind_eq_some_iff]
    | zero =>
      simp at hy₁
      rcases hf hy₁ with ⟨k, hk⟩
      exact ⟨_, Nat.le_of_lt_succ <| evaln_bound hk, _, hk, by simp⟩
    | succ y IH =>
      rcases hy₂ (Nat.succ_pos _) with ⟨a, ha, a0⟩
      rcases hf ha with ⟨k₁, hk₁⟩
      rcases IH m.succ (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
          fun {i} hi => by
          simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using
            hy₂ (Nat.succ_lt_succ hi) with
        ⟨k₂, hk₂⟩
      use (max k₁ k₂).succ
      rw [zero_add] at hk₁
      use Nat.le_succ_of_le <| le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁
      use a
      use evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
      simpa [a0, add_comm, add_left_comm] using
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂
  | _ => exact ⟨⟨_, le_rfl⟩, h.symm⟩

section
open RecursiveIn
theorem eval_eq_rfindOpt {O : ℕ → ℕ} (c n) : eval O c n = Nat.rfindOpt fun k => evaln O k c n :=
  Part.ext fun x => by
    refine evaln_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl; apply evaln_mono hl
end
end Oracle.Single
