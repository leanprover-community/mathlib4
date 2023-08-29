/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Cast.Basic

#align_import data.int.cast.lemmas from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`),
particularly results involving algebraic homomorphisms or the order structure on `ℤ`
which were not available in the import dependencies of `Data.Int.Cast.Basic`.

## Main declarations

* `castAddHom`: `cast` bundled as an `AddMonoidHom`.
* `castRingHom`: `cast` bundled as a `RingHom`.
-/


open Nat

variable {F ι α β : Type*}

namespace Int

/-- Coercion `ℕ → ℤ` as a `RingHom`. -/
def ofNatHom : ℕ →+* ℤ :=
  Nat.castRingHom ℤ
#align int.of_nat_hom Int.ofNatHom

-- Porting note: no need to be `@[simp]`, as `Nat.cast_pos` handles this.
-- @[simp]
theorem coe_nat_pos {n : ℕ} : (0 : ℤ) < n ↔ 0 < n :=
  Nat.cast_pos
#align int.coe_nat_pos Int.coe_nat_pos

theorem coe_nat_succ_pos (n : ℕ) : 0 < (n.succ : ℤ) :=
  Int.coe_nat_pos.2 (succ_pos n)
#align int.coe_nat_succ_pos Int.coe_nat_succ_pos

lemma toNat_lt' {a : ℤ} {b : ℕ} (hb : b ≠ 0) : a.toNat < b ↔ a < b := by
  rw [←toNat_lt_toNat, toNat_coe_nat]; exact coe_nat_pos.2 hb.bot_lt
  -- ⊢ 0 < ↑b
                                       -- 🎉 no goals
#align int.to_nat_lt Int.toNat_lt'

lemma natMod_lt {a : ℤ} {b : ℕ} (hb : b ≠ 0) : a.natMod b < b :=
  (toNat_lt' hb).2 $ emod_lt_of_pos _ $ coe_nat_pos.2 hb.bot_lt
#align int.nat_mod_lt Int.natMod_lt

section cast

@[simp, norm_cast]
theorem cast_mul [NonAssocRing α] : ∀ m n, ((m * n : ℤ) : α) = m * n := fun m =>
  Int.inductionOn' m 0 (by simp) (fun k _ ih n => by simp [add_mul, ih]) fun k _ ih n => by
                           -- 🎉 no goals
                                                     -- 🎉 no goals
    simp [sub_mul, ih]
    -- 🎉 no goals
#align int.cast_mul Int.cast_mulₓ -- dubious translation, type involves HasLiftT

@[simp, norm_cast]
theorem cast_ite [AddGroupWithOne α] (P : Prop) [Decidable P] (m n : ℤ) :
    ((ite P m n : ℤ) : α) = ite P (m : α) (n : α) :=
  apply_ite _ _ _ _
#align int.cast_ite Int.cast_ite

/-- `coe : ℤ → α` as an `AddMonoidHom`. -/
def castAddHom (α : Type*) [AddGroupWithOne α] : ℤ →+ α where
  toFun := Int.cast
  map_zero' := cast_zero
  map_add' := cast_add
#align int.cast_add_hom Int.castAddHom

@[simp]
theorem coe_castAddHom [AddGroupWithOne α] : ⇑(castAddHom α) = fun x : ℤ => (x : α) :=
  rfl
#align int.coe_cast_add_hom Int.coe_castAddHom

/-- `coe : ℤ → α` as a `RingHom`. -/
def castRingHom (α : Type*) [NonAssocRing α] : ℤ →+* α where
  toFun := Int.cast
  map_zero' := cast_zero
  map_add' := cast_add
  map_one' := cast_one
  map_mul' := cast_mul
#align int.cast_ring_hom Int.castRingHom

@[simp]
theorem coe_castRingHom [NonAssocRing α] : ⇑(castRingHom α) = fun x : ℤ => (x : α) :=
  rfl
#align int.coe_cast_ring_hom Int.coe_castRingHom

theorem cast_commute [NonAssocRing α] : ∀ (m : ℤ) (x : α), Commute (↑m) x
  | (n : ℕ), x => by simpa using n.cast_commute x
                     -- 🎉 no goals
  | -[n+1], x => by
    simpa only [cast_negSucc, Commute.neg_left_iff, Commute.neg_right_iff] using
      (n + 1).cast_commute (-x)
#align int.cast_commute Int.cast_commute

theorem cast_comm [NonAssocRing α] (m : ℤ) (x : α) : (m : α) * x = x * m :=
  (cast_commute m x).eq
#align int.cast_comm Int.cast_comm

theorem commute_cast [NonAssocRing α] (x : α) (m : ℤ) : Commute x m :=
  (m.cast_commute x).symm
#align int.commute_cast Int.commute_cast

theorem cast_mono [OrderedRing α] : Monotone (fun x : ℤ => (x : α)) := by
  intro m n h
  -- ⊢ (fun x => ↑x) m ≤ (fun x => ↑x) n
  rw [← sub_nonneg] at h
  -- ⊢ (fun x => ↑x) m ≤ (fun x => ↑x) n
  lift n - m to ℕ using h with k hk
  -- ⊢ ↑m ≤ ↑n
  rw [← sub_nonneg, ← cast_sub, ← hk, cast_ofNat]
  -- ⊢ 0 ≤ ↑k
  exact k.cast_nonneg
  -- 🎉 no goals
#align int.cast_mono Int.cast_mono

@[simp]
theorem cast_nonneg [OrderedRing α] [Nontrivial α] : ∀ {n : ℤ}, (0 : α) ≤ n ↔ 0 ≤ n
  | (n : ℕ) => by simp
                  -- 🎉 no goals
  | -[n+1] => by
    have : -(n : α) < 1 := lt_of_le_of_lt (by simp) zero_lt_one
    -- ⊢ 0 ≤ ↑-[n+1] ↔ 0 ≤ -[n+1]
    simpa [(negSucc_lt_zero n).not_le, ← sub_eq_add_neg, le_neg] using this.not_le
    -- 🎉 no goals
#align int.cast_nonneg Int.cast_nonneg

@[simp, norm_cast]
theorem cast_le [OrderedRing α] [Nontrivial α] {m n : ℤ} : (m : α) ≤ n ↔ m ≤ n := by
  rw [← sub_nonneg, ← cast_sub, cast_nonneg, sub_nonneg]
  -- 🎉 no goals
#align int.cast_le Int.cast_le

theorem cast_strictMono [OrderedRing α] [Nontrivial α] : StrictMono (fun x : ℤ => (x : α)) :=
  strictMono_of_le_iff_le fun _ _ => cast_le.symm
#align int.cast_strict_mono Int.cast_strictMono

@[simp, norm_cast]
theorem cast_lt [OrderedRing α] [Nontrivial α] {m n : ℤ} : (m : α) < n ↔ m < n :=
  cast_strictMono.lt_iff_lt
#align int.cast_lt Int.cast_lt

@[simp]
theorem cast_nonpos [OrderedRing α] [Nontrivial α] {n : ℤ} : (n : α) ≤ 0 ↔ n ≤ 0 := by
  rw [← cast_zero, cast_le]
  -- 🎉 no goals
#align int.cast_nonpos Int.cast_nonpos

@[simp]
theorem cast_pos [OrderedRing α] [Nontrivial α] {n : ℤ} : (0 : α) < n ↔ 0 < n := by
  rw [← cast_zero, cast_lt]
  -- 🎉 no goals
#align int.cast_pos Int.cast_pos

@[simp]
theorem cast_lt_zero [OrderedRing α] [Nontrivial α] {n : ℤ} : (n : α) < 0 ↔ n < 0 := by
  rw [← cast_zero, cast_lt]
  -- 🎉 no goals
#align int.cast_lt_zero Int.cast_lt_zero

section LinearOrderedRing

variable [LinearOrderedRing α] {a b : ℤ} (n : ℤ)

@[simp, norm_cast]
theorem cast_min : (↑(min a b) : α) = min (a : α) (b : α) :=
  Monotone.map_min cast_mono
#align int.cast_min Int.cast_min

@[simp, norm_cast]
theorem cast_max : (↑(max a b) : α) = max (a : α) (b : α) :=
  Monotone.map_max cast_mono
#align int.cast_max Int.cast_max

@[simp, norm_cast]
theorem cast_abs : ((|a| : ℤ) : α) = |(a : α)| := by simp [abs_eq_max_neg]
                                                     -- 🎉 no goals
#align int.cast_abs Int.cast_abs

theorem cast_one_le_of_pos (h : 0 < a) : (1 : α) ≤ a := by exact_mod_cast Int.add_one_le_of_lt h
                                                           -- 🎉 no goals
#align int.cast_one_le_of_pos Int.cast_one_le_of_pos

theorem cast_le_neg_one_of_neg (h : a < 0) : (a : α) ≤ -1 := by
  rw [← Int.cast_one, ← Int.cast_neg, cast_le]
  -- ⊢ a ≤ -1
  exact Int.le_sub_one_of_lt h
  -- 🎉 no goals
#align int.cast_le_neg_one_of_neg Int.cast_le_neg_one_of_neg

variable (α) {n}

theorem cast_le_neg_one_or_one_le_cast_of_ne_zero (hn : n ≠ 0) : (n : α) ≤ -1 ∨ 1 ≤ (n : α) :=
  hn.lt_or_lt.imp cast_le_neg_one_of_neg cast_one_le_of_pos
#align int.cast_le_neg_one_or_one_le_cast_of_ne_zero Int.cast_le_neg_one_or_one_le_cast_of_ne_zero

variable {α} (n)

theorem nneg_mul_add_sq_of_abs_le_one {x : α} (hx : |x| ≤ 1) : (0 : α) ≤ n * x + n * n := by
  have hnx : 0 < n → 0 ≤ x + n := fun hn => by
    have := _root_.add_le_add (neg_le_of_abs_le hx) (cast_one_le_of_pos hn)
    rwa [add_left_neg] at this
  have hnx' : n < 0 → x + n ≤ 0 := fun hn => by
    have := _root_.add_le_add (le_of_abs_le hx) (cast_le_neg_one_of_neg hn)
    rwa [add_right_neg] at this
  rw [← mul_add, mul_nonneg_iff]
  -- ⊢ 0 ≤ ↑n ∧ 0 ≤ x + ↑n ∨ ↑n ≤ 0 ∧ x + ↑n ≤ 0
  rcases lt_trichotomy n 0 with (h | rfl | h)
  · exact Or.inr ⟨by exact_mod_cast h.le, hnx' h⟩
    -- 🎉 no goals
  · simp [le_total 0 x]
    -- 🎉 no goals
  · exact Or.inl ⟨by exact_mod_cast h.le, hnx h⟩
    -- 🎉 no goals
#align int.nneg_mul_add_sq_of_abs_le_one Int.nneg_mul_add_sq_of_abs_le_one

theorem cast_natAbs : (n.natAbs : α) = |n| := by
  cases n
  -- ⊢ ↑(natAbs (ofNat a✝)) = ↑|ofNat a✝|
  · simp
    -- 🎉 no goals
  · rw [abs_eq_natAbs, natAbs_negSucc, cast_succ, cast_ofNat, cast_succ]
    -- 🎉 no goals
#align int.cast_nat_abs Int.cast_natAbs

end LinearOrderedRing

theorem coe_int_dvd [CommRing α] (m n : ℤ) (h : m ∣ n) : (m : α) ∣ (n : α) :=
  RingHom.map_dvd (Int.castRingHom α) h
#align int.coe_int_dvd Int.coe_int_dvd

end cast

end Int

open Int

namespace AddMonoidHom

variable {A : Type*}

/-- Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext high]
theorem ext_int [AddMonoid A] {f g : ℤ →+ A} (h1 : f 1 = g 1) : f = g :=
  have : f.comp (Int.ofNatHom : ℕ →+ ℤ) = g.comp (Int.ofNatHom : ℕ →+ ℤ) := ext_nat' _ _ h1
  have this' : ∀ n : ℕ, f n = g n := FunLike.ext_iff.1 this
  ext fun n => match n with
  | (n : ℕ) => this' n
  | .negSucc n => eq_on_neg _ _ (this' <| n + 1)
#align add_monoid_hom.ext_int AddMonoidHom.ext_int

variable [AddGroupWithOne A]

theorem eq_int_castAddHom (f : ℤ →+ A) (h1 : f 1 = 1) : f = Int.castAddHom A :=
  ext_int <| by simp [h1]
                -- 🎉 no goals
#align add_monoid_hom.eq_int_cast_hom AddMonoidHom.eq_int_castAddHom

end AddMonoidHom

theorem eq_intCast' [AddGroupWithOne α] [AddMonoidHomClass F ℤ α] (f : F) (h₁ : f 1 = 1) :
    ∀ n : ℤ, f n = n :=
  FunLike.ext_iff.1 <| (f : ℤ →+ α).eq_int_castAddHom h₁
#align eq_int_cast' eq_intCast'

@[simp]
theorem Int.castAddHom_int : Int.castAddHom ℤ = AddMonoidHom.id ℤ :=
  ((AddMonoidHom.id ℤ).eq_int_castAddHom rfl).symm
#align int.cast_add_hom_int Int.castAddHom_int

namespace MonoidHom

variable {M : Type*} [Monoid M]

open Multiplicative

@[ext]
theorem ext_mint {f g : Multiplicative ℤ →* M} (h1 : f (ofAdd 1) = g (ofAdd 1)) : f = g :=
  MonoidHom.toAdditive''.injective <| AddMonoidHom.ext_int <| Additive.toMul.injective h1
#align monoid_hom.ext_mint MonoidHom.ext_mint

/-- If two `MonoidHom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : ℤ →* M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidHom = g.comp Int.ofNatHom.toMonoidHom) : f = g := by
  ext (x | x)
  -- ⊢ ↑f (ofNat x) = ↑g (ofNat x)
  · exact (FunLike.congr_fun h_nat x : _)
    -- 🎉 no goals
  · rw [Int.negSucc_eq, ← neg_one_mul, f.map_mul, g.map_mul]
    -- ⊢ ↑f (-1) * ↑f (↑x + 1) = ↑g (-1) * ↑g (↑x + 1)
    congr 1
    -- ⊢ ↑f (↑x + 1) = ↑g (↑x + 1)
    exact_mod_cast (FunLike.congr_fun h_nat (x + 1) : _)
    -- 🎉 no goals
#align monoid_hom.ext_int MonoidHom.ext_int

end MonoidHom

namespace MonoidWithZeroHom

variable {M : Type*} [MonoidWithZero M]

/-- If two `MonoidWithZeroHom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : ℤ →*₀ M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidWithZeroHom = g.comp Int.ofNatHom.toMonoidWithZeroHom) :
    f = g :=
  toMonoidHom_injective <| MonoidHom.ext_int h_neg_one <|
    MonoidHom.ext (FunLike.congr_fun h_nat : _)
#align monoid_with_zero_hom.ext_int MonoidWithZeroHom.ext_int

end MonoidWithZeroHom

/-- If two `MonoidWithZeroHom`s agree on `-1` and the _positive_ naturals then they are equal. -/
theorem ext_int' [MonoidWithZero α] [MonoidWithZeroHomClass F ℤ α] {f g : F}
    (h_neg_one : f (-1) = g (-1)) (h_pos : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  (FunLike.ext _ _) fun n =>
    haveI :=
      FunLike.congr_fun
        (@MonoidWithZeroHom.ext_int _ _ (f : ℤ →*₀ α) (g : ℤ →*₀ α) h_neg_one <|
          MonoidWithZeroHom.ext_nat (h_pos _))
        n
    this
#align ext_int' ext_int'

section NonAssocRing

variable [NonAssocRing α] [NonAssocRing β]

@[simp]
theorem eq_intCast [RingHomClass F ℤ α] (f : F) (n : ℤ) : f n = n :=
  eq_intCast' f (map_one _) n
#align eq_int_cast eq_intCast

@[simp]
theorem map_intCast [RingHomClass F α β] (f : F) (n : ℤ) : f n = n :=
  eq_intCast ((f : α →+* β).comp (Int.castRingHom α)) n
#align map_int_cast map_intCast

namespace RingHom

theorem eq_intCast' (f : ℤ →+* α) : f = Int.castRingHom α :=
  RingHom.ext <| eq_intCast f
#align ring_hom.eq_int_cast' RingHom.eq_intCast'

theorem ext_int {R : Type*} [NonAssocSemiring R] (f g : ℤ →+* R) : f = g :=
  coe_addMonoidHom_injective <| AddMonoidHom.ext_int <| f.map_one.trans g.map_one.symm
#align ring_hom.ext_int RingHom.ext_int

instance Int.subsingleton_ringHom {R : Type*} [NonAssocSemiring R] : Subsingleton (ℤ →+* R) :=
  ⟨RingHom.ext_int⟩
#align ring_hom.int.subsingleton_ring_hom RingHom.Int.subsingleton_ringHom

end RingHom

end NonAssocRing

#align int.cast_id Int.cast_idₓ -- dubious translation, type involves HasLiftT?

@[simp]
theorem Int.castRingHom_int : Int.castRingHom ℤ = RingHom.id ℤ :=
  (RingHom.id ℤ).eq_intCast'.symm
#align int.cast_ring_hom_int Int.castRingHom_int

namespace Pi

variable {π : ι → Type*} [∀ i, IntCast (π i)]

instance intCast : IntCast (∀ i, π i) :=
  { intCast := fun n _ ↦ n }

theorem int_apply (n : ℤ) (i : ι) : (n : ∀ i, π i) i = n :=
  rfl
#align pi.int_apply Pi.int_apply

@[simp]
theorem coe_int (n : ℤ) : (n : ∀ i, π i) = fun _ => ↑n :=
  rfl
#align pi.coe_int Pi.coe_int

end Pi

theorem Sum.elim_intCast_intCast {α β γ : Type*} [IntCast γ] (n : ℤ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  @Sum.elim_lam_const_lam_const α β γ n
#align sum.elim_int_cast_int_cast Sum.elim_intCast_intCast

/-! ### Order dual -/


open OrderDual

instance [h : IntCast α] : IntCast αᵒᵈ :=
  h

instance [h : AddGroupWithOne α] : AddGroupWithOne αᵒᵈ :=
  h

instance [h : AddCommGroupWithOne α] : AddCommGroupWithOne αᵒᵈ :=
  h

@[simp]
theorem toDual_intCast [IntCast α] (n : ℤ) : toDual (n : α) = n :=
  rfl
#align to_dual_int_cast toDual_intCast

@[simp]
theorem ofDual_intCast [IntCast α] (n : ℤ) : (ofDual n : α) = n :=
  rfl
#align of_dual_int_cast ofDual_intCast

/-! ### Lexicographic order -/


instance [h : IntCast α] : IntCast (Lex α) :=
  h

instance [h : AddGroupWithOne α] : AddGroupWithOne (Lex α) :=
  h

instance [h : AddCommGroupWithOne α] : AddCommGroupWithOne (Lex α) :=
  h

@[simp]
theorem toLex_intCast [IntCast α] (n : ℤ) : toLex (n : α) = n :=
  rfl
#align to_lex_int_cast toLex_intCast

@[simp]
theorem ofLex_intCast [IntCast α] (n : ℤ) : (ofLex n : α) = n :=
  rfl
#align of_lex_int_cast ofLex_intCast
