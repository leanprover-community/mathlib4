/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.bitvec.basic
! leanprover-community/mathlib commit 008af8bb14b3ebef7e04ec3b0d63b947dee4d26a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors and their coercions to
`Nat` and `Fin`.
-/
namespace Bitvec

open Nat

private theorem toList_neg_one_aux : ∀ (n : ℕ),
  (List.mapAccumr (fun y c ↦ (y || c, xor y c))
    (List.replicate n false ++ [true]) false) =
    (true, List.replicate (n+1) true)
  | 0 => rfl
  | n+1 => by rw [List.replicate_succ, List.cons_append, List.mapAccumr,
    toList_neg_one_aux n]; simp


theorem neg_one : ∀ {n : ℕ}, (-1: Bitvec n) = Vector.replicate n true
  | 0 => rfl
  | n+1 => by
    show (Bitvec.one (n+1)).neg = Vector.replicate (n+1) true
    simp [Bitvec.neg, Bitvec.one, Vector.mapAccumr, Vector.replicate,
      Vector.append, List.cons_append, List.mapAccumr, toList_neg_one_aux n]


theorem toList_neg_one : ∀ {n : ℕ}, (-1 : Bitvec n).toList = List.replicate n true := by
  simp only [neg_one, Vector.replicate, Vector.toList_mk, forall_const, toList]


instance (n : ℕ) : Preorder (Bitvec n) :=
  Preorder.lift Bitvec.toNat

theorem bitsToNat_toList {n : ℕ} (x : Bitvec n) : Bitvec.toNat x = bitsToNat (Vector.toList x) :=
  rfl
#align bitvec.bits_to_nat_to_list Bitvec.bitsToNat_toList

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

attribute [local simp] Nat.zero_add Nat.add_zero Nat.one_mul Nat.mul_one Nat.zero_mul Nat.mul_zero

local infixl:65 "++ₜ" => Vector.append

-- mul_left_comm
theorem toNat_append {m : ℕ} (xs : Bitvec m) (b : Bool) :
    Bitvec.toNat (xs++ₜb ::ᵥ Vector.nil) =
      Bitvec.toNat xs * 2 + Bitvec.toNat (b ::ᵥ Vector.nil) := by
  cases' xs with xs P
  simp [bitsToNat_toList]; clear P
  unfold bitsToNat
  -- porting note: was `unfold List.foldl`, which now unfolds to an ugly match
  rw [List.foldl, List.foldl]
  -- generalize the accumulator of foldl
  generalize h : 0 = x
  conv in addLsb x b =>
    rw [← h]
  clear h
  simp
  induction' xs with x xs xs_ih generalizing x
  · simp
    unfold addLsb
    simp [Nat.mul_succ]
  · simp
    apply xs_ih
#align bitvec.to_nat_append Bitvec.toNat_append

-- Porting Note: the mathlib3port version of the proof was :
--  simp [bits_to_nat_to_list]
--  unfold bits_to_nat add_lsb List.foldl cond
--  simp [cond_to_bool_mod_two]
theorem bits_toNat_decide (n : ℕ) : Bitvec.toNat (decide (n % 2 = 1) ::ᵥ Vector.nil) = n % 2 := by
  simp [bitsToNat_toList]
  unfold bitsToNat addLsb List.foldl
  simp [Nat.cond_decide_mod_two, -Bool.cond_decide]
#align bitvec.bits_to_nat_to_bool Bitvec.bits_toNat_decide

theorem ofNat_succ {k n : ℕ} :
    Bitvec.ofNat k.succ n = Bitvec.ofNat k (n / 2)++ₜdecide (n % 2 = 1) ::ᵥ Vector.nil :=
  rfl
#align bitvec.of_nat_succ Bitvec.ofNat_succ

theorem toNat_ofNat {k n : ℕ} : Bitvec.toNat (Bitvec.ofNat k n) = n % 2 ^ k := by
  induction' k with k ih generalizing n
  · simp [Nat.mod_one]
    rfl
  · rw [ofNat_succ, toNat_append, ih, bits_toNat_decide, mod_pow_succ, Nat.mul_comm]
#align bitvec.to_nat_of_nat Bitvec.toNat_ofNat

theorem ofFin_val {n : ℕ} (i : Fin <| 2 ^ n) : (ofFin i).toNat = i.val := by
  rw [ofFin, toNat_ofNat, Nat.mod_eq_of_lt]
  apply i.is_lt
#align bitvec.of_fin_val Bitvec.ofFin_val

theorem addLsb_eq_twice_add_one {x b} : addLsb x b = 2 * x + cond b 1 0 := by
  simp [addLsb, two_mul]
#align bitvec.add_lsb_eq_twice_add_one Bitvec.addLsb_eq_twice_add_one

theorem toNat_eq_foldr_reverse {n : ℕ} (v : Bitvec n) :
    v.toNat = v.toList.reverse.foldr (flip addLsb) 0 := by rw [List.foldr_reverse]; rfl
#align bitvec.to_nat_eq_foldr_reverse Bitvec.toNat_eq_foldr_reverse

-- theorem toNat_lt {n : ℕ} (v : Bitvec n) : v.toNat < 2 ^ n := by
--   suffices : v.toNat + 1 ≤ 2 ^ n; simpa
--   rw [toNat_eq_foldr_reverse]
--   cases' v with xs h
--   dsimp [Bitvec.toNat, bitsToNat]
--   rw [← List.length_reverse] at h
--   generalize xs.reverse = ys at h
--   induction' ys with head tail ih generalizing n
--   · simp [← h]
--   · simp only [← h, pow_add, flip, List.length, List.foldr, pow_one]
--     rw [addLsb_eq_twice_add_one]
--     trans 2 * List.foldr (fun (x : Bool) (y : ℕ) => addLsb y x) 0 tail + 2 * 1
--     -- Porting note: removed `ac_mono`, `mono` calls
--     · rw [add_assoc]
--       apply Nat.add_le_add_left
--       cases head <;> simp only
--     · rw [← left_distrib]
--       rw [mul_comm _ 2]
--       apply Nat.mul_le_mul_left
--       sorry
      -- exact ih rfl
-- #align bitvec.to_nat_lt Bitvec.toNat_lt

theorem addLsb_div_two {x b} : addLsb x b / 2 = x := by
  cases b <;>
      simp only [Nat.add_mul_div_left, addLsb, ← two_mul, add_comm, Nat.succ_pos',
        Nat.mul_div_right, gt_iff_lt, zero_add, cond]
  norm_num
#align bitvec.add_lsb_div_two Bitvec.addLsb_div_two

theorem decide_addLsb_mod_two {x b} : decide (addLsb x b % 2 = 1) = b := by
  cases b <;>
      simp only [Bool.decide_iff, Nat.add_mul_mod_self_left, addLsb, ← two_mul, add_comm,
        Bool.decide_False, Nat.mul_mod_right, zero_add, cond, zero_ne_one]
#align bitvec.to_bool_add_lsb_mod_two Bitvec.decide_addLsb_mod_two

-- theorem ofNat_toNat {n : ℕ} (v : Bitvec n) : Bitvec.ofNat n v.toNat = v := by
--   cases' v with xs h
--   -- Porting note: was `ext1`
--   apply Subtype.ext
--   change Vector.toList _ = xs
--   dsimp [Bitvec.toNat, bitsToNat]
--   rw [← List.length_reverse] at h
--   sorry
--   stop
--   rw [← List.reverse_reverse xs, List.foldl_reverse]
--   generalize xs.reverse = ys at h⊢; clear xs
--   induction' ys with ys_head ys_tail ys_ih generalizing n
--   · cases h
--     simp [Bitvec.ofNat]
--   · simp only [← Nat.succ_eq_add_one, List.length] at h
--     subst n
--     simp only [Bitvec.ofNat, Vector.toList_cons, Vector.toList_nil, List.reverse_cons,
--       Vector.toList_append, List.foldr]
--     erw [addLsb_div_two, decide_addLsb_mod_two]
--     congr
--     apply ys_ih
--     rfl
-- #align bitvec.of_nat_to_nat Bitvec.ofNat_toNat

-- theorem toFin_val {n : ℕ} (v : Bitvec n) : (toFin v : ℕ) = v.toNat := by
--   rw [toFin, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt]
--   apply toNat_lt
-- #align bitvec.to_fin_val Bitvec.toFin_val

-- theorem toFin_le_toFin_of_le {n} {v₀ v₁ : Bitvec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
--   show (v₀.toFin : ℕ) ≤ v₁.toFin by
--     rw [toFin_val, toFin_val]
--     exact h
-- #align bitvec.to_fin_le_to_fin_of_le Bitvec.toFin_le_toFin_of_le

theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j :=
  show (Bitvec.ofNat n i).toNat ≤ (Bitvec.ofNat n j).toNat by
    simp only [toNat_ofNat, Nat.mod_eq_of_lt, Fin.is_lt]
    exact h
#align bitvec.of_fin_le_of_fin_of_le Bitvec.ofFin_le_ofFin_of_le

-- theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i :=
--   Fin.eq_of_veq (by simp [toFin_val, ofFin, toNat_ofNat, Nat.mod_eq_of_lt, i.is_lt])
-- #align bitvec.to_fin_of_fin Bitvec.toFin_ofFin

-- theorem ofFin_toFin {n} (v : Bitvec n) : ofFin (toFin v) = v := by
--   dsimp [ofFin]
--   rw [toFin_val, ofNat_toNat]
-- #align bitvec.of_fin_to_fin Bitvec.ofFin_toFin

instance : NatCast (Bitvec n) := ⟨Bitvec.ofNat _⟩

instance : IntCast (Bitvec n) := ⟨Bitvec.ofInt _⟩

theorem foldl_addLsb_add : ∀ (n k : ℕ) (x : List Bool),
    x.foldl addLsb (n + k) = 2 ^ x.length * k + x.foldl addLsb n
  | n, k, [] => by simp [addLsb, add_comm, add_assoc, add_left_comm]
  | n, k, a::l => by
    have : (n + k) + (n + k) + cond a 1 0 = (n + n + cond a 1 0) + (k + k) :=
      by simp [add_assoc, add_comm, add_left_comm]
    rw [List.foldl_cons, List.foldl_cons, addLsb, addLsb, this, foldl_addLsb_add _ (k + k) l]
    simp [Nat.pow_succ, two_mul, mul_add, add_mul, add_assoc]

theorem foldl_addLsb_eq_add_foldl_addLsb_zero (x : List Bool) (k : ℕ) :
    x.foldl addLsb k = 2 ^ x.length * k + x.foldl addLsb 0 := by
  rw [← foldl_addLsb_add, zero_add]

/-- Theorem useful for proving properties of `toNat` -/
theorem foldl_addLsb_cons_zero (a : Bool) (x : List Bool) :
    (a::x).foldl addLsb 0 = 2^x.length * cond a 1 0 + x.foldl addLsb 0 :=
  calc (a::x).foldl addLsb 0
     = x.foldl addLsb (0 + 0 + cond a 1 0) := rfl
   _ = _ := by rw [foldl_addLsb_add]

theorem toNat_cons (a : Bool) (x : Bitvec n) :
    Bitvec.toNat (a::ᵥx) = 2^x.length * cond a 1 0 + x.toNat := by
  rcases x with ⟨x, rfl⟩
  exact foldl_addLsb_cons_zero a x

theorem zero_def : (0 : Bitvec n) = ⟨List.replicate n false, (0 : Bitvec n).2⟩  := rfl

@[simp]
theorem toList_zero : Vector.toList (0 : Bitvec n) = List.replicate n false := rfl

@[simp]
theorem toNat_zero : ∀ {n : Nat}, (0 : Bitvec n).toNat = 0
  | 0 => rfl
  | n+1 => by simpa [Bitvec.toNat, toList_zero, bitsToNat] using @toNat_zero n

-- @[simp]
-- theorem ofNat_zero : Bitvec.ofNat w 0 = 0 := by
--   rw [← toNat_zero, ofNat_toNat]

theorem toList_one {n : ℕ} : (1 : Bitvec (n + 1)).toList = List.replicate n false ++ [true] := rfl

theorem toNat_one : ∀ {n : Nat}, (1 : Bitvec n).toNat = if n = 0 then 0 else 1
  | 0 => rfl
  | 1 => rfl
  | n+2 => by
    have := @toNat_one (n+1)
    simp only [Bitvec.toNat, bitsToNat, List.foldl, Nat.add_eq, add_zero, List.append_eq,
      List.foldl_append, add_eq_zero, and_false, ite_false, toList_one] at *
    simp only [addLsb, cond_true, add_left_eq_self, add_eq_zero, and_self] at this
    rw [foldl_addLsb_eq_add_foldl_addLsb_zero, this]
    simp [addLsb]

private theorem toNat_adc_aux : ∀ {x y: List Bool} (_h : List.length x = List.length y),
    List.foldl addLsb (addLsb 0 (List.mapAccumr₂
        (fun x y c => (Bitvec.carry x y c, Bitvec.xor3 x y c)) x y false).fst)
      (List.mapAccumr₂ (fun x y c => (Bitvec.carry x y c, Bitvec.xor3 x y c)) x y false).snd =
    List.foldl addLsb 0 x + List.foldl addLsb 0 y
| [], [], _ => rfl
| a::x, b::y, h => by
  simp only [List.length_cons, Nat.succ.injEq] at h
  rw [foldl_addLsb_cons_zero, foldl_addLsb_cons_zero, add_add_add_comm, ← toNat_adc_aux h,
    List.mapAccumr₂, foldl_addLsb_eq_add_foldl_addLsb_zero, foldl_addLsb_cons_zero,
    foldl_addLsb_eq_add_foldl_addLsb_zero _ (addLsb _ _)]
  cases a <;> cases b <;>
  simp only [Bitvec.xor3, Bool.xor_self, Bitvec.carry, Bool.xor_assoc, Bool.xor_false_left, List.length_cons,
    List.length_mapAccumr₂, h, min_self, Nat.pow_succ, Nat.mul_comm, two_mul, Bool.and_self, Bool.false_and,
    Bool.or_self, addLsb._eq_1, add_zero, cond_false, mul_zero, zero_add] <;>
  cases (List.mapAccumr₂ (fun x y c => (x && y || x && c || y && c, xor x (xor y c))) x y false).fst
    <;> simp [h]

@[simp]
theorem toNat_adc {n : Nat} {x y : Bitvec n} :
    (adc x y false).toNat = x.toNat + y.toNat := by
  rcases x with ⟨x, rfl⟩
  rcases y with ⟨y, hy⟩
  dsimp [Bitvec.toNat, bitsToNat]
  exact toNat_adc_aux hy.symm

-- theorem toNat_tail : ∀ {n : Nat} (x : Bitvec n), Bitvec.toNat x.tail = x.toNat % 2^(n-1)
--   | 0, ⟨[], _⟩ => rfl
--   | n+1, ⟨a::l, h⟩ => by
--     conv_lhs => rw [← Nat.mod_eq_of_lt (Bitvec.toNat_lt (Vector.tail ⟨a::l, h⟩))]
--     simp only [List.length_cons, Nat.succ.injEq] at h
--     simp only [Bitvec.toNat, bitsToNat, foldl_addLsb_cons_zero, Vector.toList, h]
--     simp only [Vector.tail_val, List.tail_cons, ge_iff_le, add_le_iff_nonpos_left,
--       nonpos_iff_eq_zero, add_tsub_cancel_right, mul_comm, Nat.mul_add_mod]
--     sorry

-- @[simp]
-- theorem toNat_add {n : Nat} (x y : Bitvec n) : (x + y).toNat = (x.toNat + y.toNat) % 2^n := by
--   show Bitvec.toNat (x.adc y false).tail = (x.toNat + y.toNat) % 2^n
--   rw [toNat_tail, toNat_adc, add_tsub_cancel_right]

theorem add_eq_or_of_and_eq_zero_aux₁ : ∀ {x y : List Bool} (_ : x.length = y.length),
    x.zipWith (. && .) y = List.replicate x.length false →
    (x.mapAccumr₂ (fun a b c => (Bitvec.carry a b c, Bitvec.xor3 a b c)) y false).fst = false
  | [], [], _ => fun _ => rfl
  | a::x, b::y, h => fun h' => by
    simp only [List.zipWith, Bool.forall_bool, List.replicate, Nat.add_eq, add_zero,
      List.cons.injEq, Bool.and_eq_false_eq_eq_false_or_eq_false] at h'
    have := add_eq_or_of_and_eq_zero_aux₁ (Nat.succ.inj h) h'.2
    unfold Bitvec.carry at this
    rcases h'.1 with rfl | rfl <;>
    simp [List.mapAccumr₂, Bitvec.carry, this]

theorem add_eq_or_of_and_eq_zero_aux₂ : ∀ {x y : List Bool} (_ : x.length = y.length),
    x.zipWith (. && .) y = List.replicate x.length false →
    (x.mapAccumr₂ (fun a b c => (Bitvec.carry a b c, Bitvec.xor3 a b c)) y false).snd =
    x.zipWith (. || .) y
  | [], [], _ => fun _ => rfl
  | a::x, b::y, h => fun h' => by
    dsimp [List.mapAccumr₂]
    simp only [List.zipWith, Bool.forall_bool, List.replicate, Nat.add_eq, add_zero,
      List.cons.injEq, Bool.and_eq_false_eq_eq_false_or_eq_false] at h'
    rw [add_eq_or_of_and_eq_zero_aux₁ (Nat.succ.inj h) h'.2,
      add_eq_or_of_and_eq_zero_aux₂ (Nat.succ.inj h) h'.2]
    rcases h'.1 with rfl | rfl <;>
    simp [List.mapAccumr₂, Bitvec.carry, Bitvec.xor3]

theorem add_eq_or_of_and_eq_zero {n : ℕ} {x y : Bitvec n} (hxy : x.and y = 0) : x + y = x.or y :=
  Subtype.ext (add_eq_or_of_and_eq_zero_aux₂ (x.2.trans y.2.symm)
    (by convert congr_arg Vector.toList hxy; simp))

section get

@[simp]
theorem get_succ : get (b ::ᵥ v) (Fin.succ i) = get v i := by
  rfl

@[simp]
theorem get_zero : get (b ::ᵥ v) 0 = b := by
  rfl


@[simp]
theorem get_succ' : get (⟨b :: v, h⟩) (Fin.succ i) = get ⟨v, h'⟩ i := by
  rfl

@[simp]
theorem get_zero' : get (⟨b :: v, h⟩) (0 : Fin <| _ + 1) = b := by
  rfl



instance {n : Nat} : GetElem (Bitvec n) (Fin n) Bool (fun _ _ => True) where
  getElem := fun x i _ => get x i

instance {n : Nat} : GetElem (Bitvec n) Nat Bool (fun _ i => i < n) where
  getElem := fun x i h => get x ⟨i,h⟩

end get


instance (n : Nat) : Inhabited (Bitvec n) :=
  ⟨Vector.replicate n true⟩

/-- Two `v w : Bitvec n` are equal iff they are equal at every single index. -/
@[ext]
theorem ext : ∀ {v w : Bitvec n} (_ : ∀ m : Fin n, Bitvec.get v m = Bitvec.get w m), v = w
  | ⟨v, hv⟩, ⟨w, hw⟩, h =>
    Subtype.eq (List.ext_get (by rw [hv, hw]) fun m hm _ => h ⟨m, hv ▸ hm⟩)

-- I tried to use the `ext` tactic, but it inconveniently picked this theorem,
-- instead of the above one, so I removed the `@[ext]` attribute
-- @[ext]
theorem ext_nat : ∀ {v w : Bitvec n} (_ : ∀ m : Nat, Bitvec.get? v m = Bitvec.get? w m), v = w := by
  intros v w h
  apply ext
  intro ⟨m, hm⟩
  have h' := h m
  simp [get?, Option.isSome_iff_exists, hm] at h'
  apply h'

def Fun (width : Nat) := Fin width → Bool

/-- convert `Fin n → Bool` to `Bitvec n` -/
def ofFun {width : Nat} : Fun width → Bitvec width :=
  fun f => match width with
    | 0 => ⟨List.nil, rfl⟩
    | n + 1 => f (n + 1) ::ᵥ @ofFun n (fun i => f <| Fin.succ i)


@[ext]
theorem Fun.ext {f f' : Fun n} : (∀ i, f i = f' i) → f = f' :=
  funext

@[simp]
theorem get_ofFun {width : Nat} {f : Fun width} : get (ofFun f) = f := by
  funext i
  induction width
  case zero =>
    exact Fin.elim0 i
  case succ n ih =>
    simp only [ofFun]
    cases i using Fin.induction
    <;> simp[ih]

@[simp]
theorem ofFun_get {width : Nat} {v : Bitvec width} : ofFun (get v) = v := by
  ext i
  induction width
  case x.zero =>
    exact Fin.elim0 i
  case x.succ n ih =>
    simp [ofFun]
    cases i using Fin.induction
    <;> simp[ih]


instance : Equiv (Bitvec n) (Fun n) where
  toFun := get
  invFun := ofFun
  left_inv := by simp[Function.LeftInverse, ofFun_get]
  right_inv := by simp[Function.RightInverse, Function.LeftInverse, get_ofFun]


theorem eq_if_coeffs_eq {width : Nat} {x y : Bitvec width} : x = y ↔ ∀ i : Fin width, get x i = get y i := by
  constructor
  case mp =>
    intro h i
    rw [h]
  case mpr =>
    exact ext


instance {width : Nat} : Coe (Fun width) (Bitvec width) := ⟨@ofFun width⟩
instance {width : Nat} : Coe (Bitvec width) (Fun width) := ⟨@get width⟩

def ofVector : Vector Bool n → Bitvec n := id


@[simp]
theorem get_map : get (Vector.map f v) i = f (get v i) := by
  simp only [get, Vector.get_map]

@[simp]
theorem get_map₂ : get (Vector.map₂ f v₁ v₂) i = f (get v₁ i) (get v₂ i) := by
  simp only [get, Vector.get_map₂]

@[simp]
theorem get_replicate_val_eq_val : get (Vector.replicate n val) i = val := by
  induction n
  case zero =>
    exact Fin.elim0 i
  case succ n ih =>
    cases i using Fin.cases
    case H0 => rfl
    case Hs => apply ih

/-- Every bit in `zero` is `0`/`false` -/
@[simp]
theorem get_zeroes_eq_false : get (Bitvec.zero n) i = false :=
  get_replicate_val_eq_val

@[simp]
theorem get_zero_eq_false : get 0 i = false :=
  get_replicate_val_eq_val

/-- Every bit in `ones` is `1`/`true` -/
@[simp]
theorem get_ones_eq_true : get (allOnes n) i = true :=
  get_replicate_val_eq_val

/-- The all-ones bit pattern is also spelled `-1` -/
@[simp]
theorem get_minus_one : get (-1 : Bitvec n) i = true := by
  rw[neg_one]; apply get_ones_eq_true


/-!
  Show how the bitwise operations reduce to Boolean operation on individual bits
-/
section Bitwise
  variable (x y : Bitvec n)

  @[simp]
  theorem get_or : get (x.or y) i = (get x i || get y i) := by
    simp only [Bitvec.or, get_map₂]

  @[simp]
  theorem get_and : get (x.and y) i = (get x i && get y i) := by
    simp only [Bitvec.and, get_map₂]

  @[simp]
  theorem get_xor : get (x.xor y) i = xor (get x i) (get y i) := by
    simp only [Bitvec.xor, get_map₂]

  @[simp]
  theorem get_not : get (Bitvec.not x) i = not (get x i) := by
    simp only [Bitvec.not, get_map]
end Bitwise






end Bitvec
