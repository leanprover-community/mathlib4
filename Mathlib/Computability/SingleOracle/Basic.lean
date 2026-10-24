/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
module

public import Mathlib.Computability.SingleOracle.Encoding

import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.PFun
import Mathlib.Tactic.Computability.Basic

/-!
# Notations, helper functions

In this file we define helper functions which will be used in later computability arguments.
-/

@[expose] public section

open Nat Oracle.Single.Code

-- general helper functions
section pair
/-- `⟪x, y⟫` is notation for `Nat.pair x y`. -/
notation "⟪"x","y"⟫"         => Nat.pair x y
/-- Shorthand for pairs of monadic values (e.g. in `Part`). -/
notation "⟪"x","y"⟫"         => Nat.pair <$> x <*> y
/-- `⟪x, y, z⟫` is notation for 3-tuples encoded as `Nat.pair x (Nat.pair y z)`. -/
notation "⟪"x","y","z"⟫"     => Nat.pair x (Nat.pair y z)
/-- Shorthand for triples of monadic values (e.g. in `Part`). -/
notation "⟪"x","y","z"⟫"     => Nat.pair <$> x <*> (Nat.pair <$> y <*> z)
/-- `⟪x, y, z, w⟫` is notation for 4-tuples encoded as `Nat.pair (Nat.pair x y) (Nat.pair z w)`. -/
notation "⟪"x","y","z","w"⟫" => Nat.pair (Nat.pair x y) (Nat.pair z w)
/-- Shorthand for 4-tuples of monadic values (e.g. in `Part`). -/
notation "⟪"x","y","z","w"⟫" => Nat.pair <$> (Nat.pair <$> x <*> y) <*> (Nat.pair <$> z <*> w)
/-
as the left and right projection functions are commonly used,
we define shorter aliases for them:
-/
/-- The left component of `n`, viewed as a pair: `n.unpair.1`. -/
def Nat.left (n : ℕ) := n.unpair.1
/-- The right component of `n`, viewed as a pair: `n.unpair.2`. -/
def Nat.right (n : ℕ) := n.unpair.2
-- pair_l and pair_r are useful for evp_simps particularly in cov_rec proofs in
-- `Computability.Constructions.CovRec.lean`
@[simp, evp_simps] theorem pair_l {x y} : (Nat.pair x y).left = x := by simp [Nat.left]
@[simp, evp_simps] theorem pair_r {x y} : (Nat.pair x y).right = y := by simp [Nat.right]
theorem pair_lr {x} : (Nat.pair x.left x.right) = x := by simp [Nat.right, Nat.left]
theorem unpair1_to_l {n : ℕ} : (n.unpair.1) = n.left := by simp [Nat.left]
theorem unpair2_to_r {n : ℕ} : (n.unpair.2) = n.right := by simp [Nat.right]
-- scoped, so that they don't change the simp normal form of `Nat.unpair` outside this library
namespace Oracle.Single
attribute [scoped simp] pair_lr unpair1_to_l unpair2_to_r
end Oracle.Single
/-- `unpaired2 f n` applies the binary function `f` to the two components of `n`:
`f n.left n.right`. -/
@[simp, reducible] def Nat.unpaired2 {α} (f : ℕ → ℕ → α) (n : ℕ) : α := f n.left n.right
@[simp] theorem pair_pos_of_right {x s : ℕ} : ⟪x, s+1⟫ > 0 := by
  apply zero_lt_of_ne_zero
  rewrite [show 0 = Nat.pair 0 0 from rfl]
  simp [Nat.pair_eq_pair]
@[simp] theorem pair_pos_of_left {x s : ℕ} : ⟪s+1, x⟫ > 0 := by
  apply zero_lt_of_ne_zero
  rewrite [show 0 = Nat.pair 0 0 from rfl]
  simp [Nat.pair_eq_pair]
theorem pair_pos_of_right_pos {x y} (h : x > 0) : (Nat.pair y x) > 0 := by
  rw [(Nat.sub_eq_iff_eq_add h).mp rfl]; simp
theorem pair_pos_of_left_pos {x y} (h : x > 0) : (Nat.pair x y) > 0 := by
  rw [(Nat.sub_eq_iff_eq_add h).mp rfl]; simp
end pair

-- we define several conveniences to encode/decode from naturals to various types.
section conversions
/-- Decodes a natural number as a list of naturals, via `Denumerable.ofNat`. -/
abbrev Nat.n2l : ℕ → List ℕ := @Denumerable.ofNat (List ℕ) _
/-- Encodes a list of naturals as a natural number, via `Encodable.encode`. This is the inverse of
`n2l`. -/
abbrev Nat.l2n : List ℕ → ℕ := @Encodable.encode (List ℕ) _
namespace Oracle.Single
/-- Numerals of type `List ℕ` denote the list they encode: `(n : List ℕ)` is `n2l n`. -/
scoped instance instOfNatListNat {lN} : OfNat (List ℕ) lN where ofNat := n2l lN
/-- Coerces a natural number to the list it encodes, via `n2l`. -/
scoped instance instCoeNatList : Coe ℕ (List ℕ) := ⟨n2l⟩
/-- Coerces a list of naturals to its encoding, via `l2n`. -/
scoped instance instCoeListNat : Coe (List ℕ) ℕ := ⟨l2n⟩
end Oracle.Single

/-- Converts a natural number to a boolean: `0` is `false`, and everything else is `true`. -/
def n2b (n : ℕ) : Bool := if n = 0 then false else true
/-- Converts a boolean to a natural number: `true` is `1` and `false` is `0`. -/
def b2n (b : Bool) : ℕ := if b then 1 else 0
/-- Converts a natural number to a boolean, with the opposite convention to `n2b`: `0` is `true`,
and everything else is `false`. -/
def n2b' (n : ℕ) : Bool := if n=0 then true else false
/-- Converts a boolean to a natural number, with the opposite convention to `b2n`: `true` is `0` and
`false` is `1`. -/
def b'2n (b : Bool) : ℕ := if b then 0 else 1
theorem b2n_a0 {x} : b2n x = 0 ↔ x = false := by simp [b2n]

open Denumerable Encodable
/-- Decodes a natural number as an `Option ℕ`: `0` is `none`, and `n + 1` is `some n`. -/
abbrev n2o := @ofNat (Option ℕ) _
/-- Encodes an `Option ℕ` as a natural number. This is the inverse of `n2o`. -/
abbrev o2n := @encode (Option ℕ) _
@[simp] theorem encode_zero_opt : (Denumerable.ofNat (Option ℕ) 0) = Option.none := rfl
@[simp] theorem encode_succ_opt {x} : (Denumerable.ofNat (Option ℕ) (x+1)) = Option.some (x) := rfl

namespace Oracle.Single.Code.NcToNn
/-- Turns a function `ℕ → Code` into a function `ℕ → ℕ`, by encoding its outputs with `c2n`. This is
registered as a coercion. -/
@[coe] protected def lift (f : ℕ → Code) : ℕ → ℕ := fun x => c2n (f x)
instance : Coe (ℕ → Code) (ℕ → ℕ) := ⟨Oracle.Single.Code.NcToNn.lift⟩
end Oracle.Single.Code.NcToNn
namespace Oracle.Single.Code.CcToNn
/-- Turns a function `Code → Code` into a function `ℕ → ℕ`, by decoding its inputs with `n2c` and
encoding its outputs with `c2n`. This is registered as a coercion. -/
@[coe] protected def lift (f : Code → Code) : ℕ → ℕ := c2n ∘ f ∘ n2c
instance : Coe (Code → Code) (ℕ → ℕ) := ⟨Oracle.Single.Code.CcToNn.lift⟩
end Oracle.Single.Code.CcToNn
end conversions

section primrec
-- templates for primrec constructions as codes
namespace Oracle.Single.Code
/-- `IsPrim c` holds if the code `c` is built only from the primitive recursive constructors, i.e.
without `rfind'`. Such codes are total (`prim_total`), and their evaluation agrees with `evalp`
(`evalp_eq_eval`). -/
@[aesop safe, cp] inductive IsPrim : Code → Prop
| zero : IsPrim zero
| succ : IsPrim succ
| left : IsPrim left
| right : IsPrim right
| oracle : IsPrim oracle
| pair {a b : Code} (ha : IsPrim a) (hb : IsPrim b) : IsPrim (pair a b)
| comp {a b : Code} (ha : IsPrim a) (hb : IsPrim b) : IsPrim (comp a b)
| prec {a b : Code} (ha : IsPrim a) (hb : IsPrim b) : IsPrim (prec a b)
@[cp] theorem zero_prim : IsPrim zero := IsPrim.zero
@[cp] theorem succ_prim : IsPrim succ := IsPrim.succ
@[cp] theorem left_prim : IsPrim left := IsPrim.left
@[cp] theorem right_prim : IsPrim right := IsPrim.right
@[cp] theorem oracle_prim : IsPrim oracle := IsPrim.oracle
@[cp] theorem pair_prim {a b} (ha : IsPrim a) (hb : IsPrim b) : IsPrim (pair a b) :=
  IsPrim.pair ha hb
@[cp] theorem comp_prim {a b} (ha : IsPrim a) (hb : IsPrim b) : IsPrim (comp a b) :=
  IsPrim.comp ha hb
@[cp] theorem prec_prim {a b} (ha : IsPrim a) (hb : IsPrim b) : IsPrim (prec a b) :=
  IsPrim.prec ha hb
/-- `IsTotal O c` holds if the code `c` halts on every input, relative to the oracle `O`. -/
def IsTotal (O) (c : Code) := ∀x, (eval O c x).Dom
@[simp] theorem zero_total {O : ℕ → ℕ} : IsTotal O zero := fun _ ↦ trivial
@[simp] theorem left_total {O : ℕ → ℕ} : IsTotal O left := fun _ ↦ trivial
@[simp] theorem right_total {O : ℕ → ℕ} : IsTotal O right := fun _ ↦ trivial
@[simp] theorem succ_total {O : ℕ → ℕ} : IsTotal O succ := fun _ ↦ trivial
@[simp] theorem oracle_total {O : ℕ → ℕ} : IsTotal O oracle := fun _ ↦ trivial
theorem prim_total {O : ℕ → ℕ} {c} (h : IsPrim c) : IsTotal O c := by
  unfold IsTotal
  induction h with
  | zero                   => simp [eval];
  | succ                   => simp [eval];
  | left                   => simp [eval];
  | right                  => simp [eval];
  | oracle                 => simp [eval];
  | pair ha hb ha_ih hb_ih => simpa [eval, Seq.seq] using fun x ↦ ⟨ha_ih x, hb_ih x⟩
  | comp ha hb ha_ih hb_ih =>
    simp only [eval]
    intro x
    use hb_ih x
    (expose_names; exact ha_ih ((eval O b x).get (hb_ih x)))
  | prec ha hb ha_ih hb_ih =>
    expose_names
    simp only [eval, unpaired, unpair1_to_l, Part.bind_eq_bind, unpair2_to_r]
    intro x
    induction x.right with
    | zero => exact ha_ih x.left
    | succ y' IH' => use IH'; apply hb_ih
/-- Evaluates a code as a total function `ℕ → ℕ`, relative to the oracle `O`. It agrees with `eval`
on codes satisfying `IsPrim` (`evalp_eq_eval`). `rfind'` is sent to the constant function `0`. -/
@[simp, evp_simps] def evalp (O : ℕ → ℕ) : Code → ℕ → ℕ
| zero       => fun _ ↦ 0
| succ       => Nat.succ
| left       => Nat.left
| right      => Nat.right
| oracle     => O
| pair cf cg => fun x ↦ Nat.pair (evalp O cf x) (evalp O cg x)
| comp cf cg => fun x ↦ evalp O cf (evalp O cg x)
| prec cf cg => unpaired fun z n =>
  n.rec (evalp O cf z) fun y IH => (evalp O cg) (z.pair (y.pair IH))
| rfind' _   => fun _ ↦ 0
set_option backward.isDefEq.respectTransparency false in
theorem evalp_eq_eval {O : ℕ → ℕ} {c} (h : IsPrim c) : evalp O c = eval O c := by
  induction h with
  | zero => exact rfl
  | succ => exact rfl
  | left => exact rfl
  | right => exact rfl
  | oracle => exact rfl
  | pair ha hb ha_ih hb_ih =>
    unfold evalp
    simp only [eval, Part.map_eq_map]
    funext xs
    simp only [PFun.coe_val, Seq.seq, Part.bind_map]
    expose_names
    have a0 : eval O a xs = Part.some (evalp O a xs) := congrFun (_root_.id (Eq.symm ha_ih)) xs
    have a1 : eval O b xs = Part.some (evalp O b xs) := congrFun (_root_.id (Eq.symm hb_ih)) xs
    simp [a0, a1]
  | comp ha hb ha_ih hb_ih =>
    unfold evalp
    simp only [eval, Part.bind_eq_bind]
    funext xs
    expose_names
    have a0 : eval O b xs = Part.some (evalp O b xs) := congrFun (_root_.id (Eq.symm hb_ih)) xs
    have a1 : eval O a (evalp O b xs) = Part.some (evalp O a (evalp O b xs)) :=
      congrFun (_root_.id (Eq.symm ha_ih)) (evalp O b xs)
    simp [a0, a1]
  | prec ha hb ha_ih hb_ih =>
    unfold evalp
    simp only [eval, Part.bind_eq_bind]
    funext xs
    simp only [PFun.coe_val, unpaired, unpair1_to_l, unpair2_to_r]
    expose_names
    induction xs.right with
    | zero =>
      have a0 : eval O a xs.left = Part.some (evalp O a xs.left) :=
        congrFun (_root_.id (Eq.symm ha_ih)) xs.left
      simp [a0]
    | succ y' IH' =>
      have h0 : @Nat.rec
        (fun x ↦ Part ℕ)
        (eval O a xs.left)
        (fun y IH ↦ IH.bind fun i ↦ eval O b (Nat.pair xs.left (Nat.pair y i)))
        (y'+1) = ((@Nat.rec (fun x ↦ Part ℕ) (eval O a xs.left)
        (fun y IH ↦ IH.bind fun i ↦ eval O b (Nat.pair xs.left (Nat.pair y i))) y').bind
        fun i ↦ eval O b (Nat.pair xs.left (Nat.pair y' i))) := rfl
      rewrite [h0]
      rewrite [←IH']
      rewrite [Part.bind_some]
      simp only
      let prev_input :=
        Nat.pair xs.left <|
        Nat.pair y'
        (Nat.rec (evalp O a xs.left) (fun y IH ↦ evalp O b (Nat.pair xs.left (Nat.pair y IH))) y')
      have a0 :
        eval O b
        prev_input =
        Part.some (evalp O b prev_input) := congrFun (_root_.id (Eq.symm hb_ih)) prev_input
      rw [a0]
theorem evalp_eq_eval_ext {O : ℕ → ℕ} {c : Code} {x : ℕ} (h : IsPrim c) :
  eval O c x = evalp O c x := congrFun (_root_.id (Eq.symm (@evalp_eq_eval O c h))) x
@[simp 1000] theorem isPrim_prop {O : ℕ → ℕ} {c} : PrimrecIn O (evalp O c) := by
  induction c with
  | zero => exact PrimrecIn.zero
  | succ => exact PrimrecIn.succ
  | left => exact PrimrecIn.left
  | right => exact PrimrecIn.right
  | oracle => exact PrimrecIn.oracle
  | pair ha hb ha_ih hb_ih => unfold evalp; exact PrimrecIn.pair ha_ih hb_ih
  | comp ha hb ha_ih hb_ih => unfold evalp; exact PrimrecIn.comp ha_ih hb_ih
  | prec ha hb ha_ih hb_ih => unfold evalp; exact PrimrecIn.prec ha_ih hb_ih
  | rfind' ha ha_ih => exact PrimrecIn.zero
theorem isPrim_of_primrecIn {O f} (h : PrimrecIn O f) : ∃ c, IsPrim c ∧ f=evalp O c := by
  induction h with
  | zero => use Code.zero; exact ⟨IsPrim.zero,rfl⟩
  | succ => use Code.succ; exact ⟨IsPrim.succ,rfl⟩
  | left => use Code.left; exact ⟨IsPrim.left,rfl⟩
  | right => use Code.right; exact ⟨IsPrim.right,rfl⟩
  | oracle => use Code.oracle; exact ⟨IsPrim.oracle,rfl⟩
  | pair pf pg ef eg =>
    rcases ef with ⟨cf,hcf⟩
    rcases eg with ⟨cg,hcg⟩
    use Code.pair cf cg;
    constructor
    · exact IsPrim.pair hcf.left hcg.left
    · simp only [evalp]; rw [hcf.right, hcg.right]
  | comp pf pg ef eg =>
    rcases ef with ⟨cf,hcf⟩
    rcases eg with ⟨cg,hcg⟩
    use Code.comp cf cg;
    constructor
    · exact IsPrim.comp hcf.left hcg.left
    · simp only [evalp]; rw [hcf.right, hcg.right]
  | prec pf pg ef eg =>
    rcases ef with ⟨cf,hcf⟩
    rcases eg with ⟨cg,hcg⟩
    use Code.prec cf cg;
    constructor
    · exact IsPrim.prec hcf.left hcg.left
    · simp only [evalp]; rw [hcf.right, hcg.right]
end Oracle.Single.Code
end primrec

section total
namespace Oracle.Single.Code
/-- A total evaluation function, requiring proof that the given code is total. -/
def evalt (O : ℕ → ℕ) (c : Code) (h : IsTotal O c) : ℕ → ℕ := fun x ↦ (eval O c x).get (h x)
theorem total_pair_iff {O cf cg} :
    (IsTotal O cf) ∧ (IsTotal O cg) ↔ (IsTotal O (pair cf cg)) :=
  ⟨
    fun h x ↦ ⟨h.left x, h.right x⟩,
    fun h ↦ ⟨fun x ↦ Part.left_dom_of_sub_dom (h x) , fun x ↦ Part.right_dom_of_div_dom (h x)⟩
  ⟩
@[simp] theorem total_pair_of {O cf cg} (hcf : IsTotal O cf) (hcg : IsTotal O cg) :
  (IsTotal O (pair cf cg)) := total_pair_iff.mp ⟨hcf,hcg⟩
theorem total_comp_of {O cf cg} (hcf : IsTotal O cf) (hcg : IsTotal O cg) :
    (IsTotal O (comp cf cg)) := by
  intro x
  simp only [eval]
  use hcg x
  exact hcf ((eval O cg x).get (hcg x))
theorem total_of_pair_left {O cf cg} (h : IsTotal O (pair cf cg)) : IsTotal O cf :=
  (total_pair_iff.mpr h).left
theorem total_of_pair_right {O cf cg} (h : IsTotal O (pair cf cg)) : IsTotal O cg :=
  (total_pair_iff.mpr h).right
theorem total_of_comp_left {O cf cg} (h : IsTotal O (comp cf cg)) : IsTotal O cg := by
  intro h2
  exact Part.Dom.of_bind (h h2)
@[simp] theorem total_of_comp_right {O cf cg} (h : IsTotal O (comp cf cg)) :
    ∀ x, (eval O cf ((eval O cg x).get (Part.Dom.of_bind (h x)))).Dom := by
  exact fun x ↦ Part.right_dom_of_div_dom (h x)
theorem total_of_prec_left {O cf cg} (h : IsTotal O (prec cf cg)) : IsTotal O cf := by
  intro x
  unfold IsTotal at h
  simp only [eval, unpaired, unpair1_to_l, Part.bind_eq_bind, unpair2_to_r] at h
  have hx := h (Nat.pair x 0)
  simp only [pair_l, pair_r, rec_zero] at hx
  exact hx
theorem eval_total_comp {O cf cg x} (h : IsTotal O (comp cf cg)) :
    eval O (comp cf cg) x =
    Part.some
    ((eval O cf ((eval O cg x).get (Part.Dom.of_bind (h x)))).get (total_of_comp_right h x)) := by
  simp only [eval, Part.some_get]
  exact Part.Dom.bind (Part.Dom.of_bind (h x)) (eval O cf)
end Oracle.Single.Code
end total

namespace Oracle.Single.Code
@[simp 1000] theorem RecursiveIn_of_eval {O c} : RecursiveIn O (eval O c) := by
  induction c with
  | zero => exact RecursiveIn.zero
  | succ => exact RecursiveIn.succ
  | left => exact RecursiveIn.left
  | right => exact RecursiveIn.right
  | oracle => exact RecursiveIn.oracle
  | pair ha hb ha_ih hb_ih => exact RecursiveIn.pair ha_ih hb_ih
  | comp ha hb ha_ih hb_ih => exact RecursiveIn.comp ha_ih hb_ih
  | prec ha hb ha_ih hb_ih => exact RecursiveIn.prec ha_ih hb_ih
  | rfind' ha ha_ih => exact RecursiveIn.rfind ha_ih
end Oracle.Single.Code
