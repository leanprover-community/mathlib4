/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Hom.Ring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Algebra.Group.Opposite

#align_import data.nat.cast.basic from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`Nat.cast`).

## Main declarations

* `castAddMonoidHom`: `cast` bundled as an `AddMonoidHom`.
* `castRingHom`: `cast` bundled as a `RingHom`.
-/

-- Porting note: There are many occasions below where we need `simp [map_zero f]`
-- where `simp [map_zero]` should suffice. (Similarly for `map_one`.)
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simp.20regression.20with.20MonoidHomClass

variable {α β : Type*}

namespace Nat

/-- `Nat.cast : ℕ → α` as an `AddMonoidHom`. -/
def castAddMonoidHom (α : Type*) [AddMonoidWithOne α] :
    ℕ →+ α where
  toFun := Nat.cast
  map_add' := cast_add
  map_zero' := cast_zero
#align nat.cast_add_monoid_hom Nat.castAddMonoidHom

@[simp]
theorem coe_castAddMonoidHom [AddMonoidWithOne α] : (castAddMonoidHom α : ℕ → α) = Nat.cast :=
  rfl
#align nat.coe_cast_add_monoid_hom Nat.coe_castAddMonoidHom

@[simp, norm_cast]
theorem cast_mul [NonAssocSemiring α] (m n : ℕ) : ((m * n : ℕ) : α) = m * n := by
  induction n <;> simp [mul_succ, mul_add, *]
  -- ⊢ ↑(m * zero) = ↑m * ↑zero
                  -- 🎉 no goals
                  -- 🎉 no goals
#align nat.cast_mul Nat.cast_mul

/-- `Nat.cast : ℕ → α` as a `RingHom` -/
def castRingHom (α : Type*) [NonAssocSemiring α] : ℕ →+* α :=
  { castAddMonoidHom α with toFun := Nat.cast, map_one' := cast_one, map_mul' := cast_mul }
#align nat.cast_ring_hom Nat.castRingHom

@[simp]
theorem coe_castRingHom [NonAssocSemiring α] : (castRingHom α : ℕ → α) = Nat.cast :=
  rfl
#align nat.coe_cast_ring_hom Nat.coe_castRingHom

theorem cast_commute [NonAssocSemiring α] (n : ℕ) (x : α) : Commute (n : α) x := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Commute.zero_left x
  | succ n ihn => rw [Nat.cast_succ]; exact ihn.add_left (Commute.one_left x)
#align nat.cast_commute Nat.cast_commute

theorem _root_.Commute.ofNat_left [NonAssocSemiring α] (n : ℕ) [n.AtLeastTwo] (x : α) :
    Commute (OfNat.ofNat n) x :=
  n.cast_commute x

theorem cast_comm [NonAssocSemiring α] (n : ℕ) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).eq
#align nat.cast_comm Nat.cast_comm

theorem commute_cast [NonAssocSemiring α] (x : α) (n : ℕ) : Commute x n :=
  (n.cast_commute x).symm
#align nat.commute_cast Nat.commute_cast

theorem _root_.Commute.ofNat_right [NonAssocSemiring α] (x : α) (n : ℕ) [n.AtLeastTwo] :
    Commute x (OfNat.ofNat n) :=
  n.commute_cast x

section OrderedSemiring
/- Note: even though the section indicates `OrderedSemiring`, which is the common use case,
we use a generic collection of instances so that it applies in other settings (e.g., in a
`StarOrderedRing`, or the `selfAdjoint` or `StarOrderedRing.positive` parts thereof). -/

variable [AddCommMonoidWithOne α] [PartialOrder α]
variable [CovariantClass α α (· + ·) (· ≤ ·)] [ZeroLEOneClass α]

@[mono]
theorem mono_cast : Monotone (Nat.cast : ℕ → α) :=
  monotone_nat_of_le_succ fun n ↦ by
    rw [Nat.cast_succ]; exact le_add_of_nonneg_right zero_le_one
    -- ⊢ ↑n ≤ ↑n + 1
                        -- 🎉 no goals
#align nat.mono_cast Nat.mono_cast

@[simp low]
theorem cast_nonneg' (n : ℕ) : 0 ≤ (n : α) :=
  @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)

-- without this more specific version Lean often chokes
@[simp]
theorem cast_nonneg {α} [OrderedSemiring α] (n : ℕ) : 0 ≤ (n : α) :=
  cast_nonneg' n
#align nat.cast_nonneg Nat.cast_nonneg

section Nontrivial

variable [NeZero (1 : α)]

theorem cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 :=
  zero_lt_one.trans_le <| le_add_of_nonneg_left n.cast_nonneg'
#align nat.cast_add_one_pos Nat.cast_add_one_pos

@[simp low]
theorem cast_pos' {n : ℕ} : (0 : α) < n ↔ 0 < n := by cases n <;> simp [cast_add_one_pos]
                                                      -- ⊢ 0 < ↑zero ↔ 0 < zero
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals

-- without this more specific version Lean often chokes
@[simp]
theorem cast_pos {α} [OrderedSemiring α] [Nontrivial α] {n : ℕ} : (0 : α) < n ↔ 0 < n := cast_pos'
#align nat.cast_pos Nat.cast_pos

end Nontrivial

variable [CharZero α] {m n : ℕ}

theorem strictMono_cast : StrictMono (Nat.cast : ℕ → α) :=
  mono_cast.strictMono_of_injective cast_injective
#align nat.strict_mono_cast Nat.strictMono_cast

/-- `Nat.cast : ℕ → α` as an `OrderEmbedding` -/
@[simps! (config := { fullyApplied := false })]
def castOrderEmbedding : ℕ ↪o α :=
  OrderEmbedding.ofStrictMono Nat.cast Nat.strictMono_cast
#align nat.cast_order_embedding Nat.castOrderEmbedding
#align nat.cast_order_embedding_apply Nat.castOrderEmbedding_apply

@[simp, norm_cast]
theorem cast_le : (m : α) ≤ n ↔ m ≤ n :=
  strictMono_cast.le_iff_le
#align nat.cast_le Nat.cast_le

@[simp, norm_cast, mono]
theorem cast_lt : (m : α) < n ↔ m < n :=
  strictMono_cast.lt_iff_lt
#align nat.cast_lt Nat.cast_lt

@[simp, norm_cast]
theorem one_lt_cast : 1 < (n : α) ↔ 1 < n := by rw [← cast_one, cast_lt]
                                                -- 🎉 no goals
#align nat.one_lt_cast Nat.one_lt_cast

@[simp, norm_cast]
theorem one_le_cast : 1 ≤ (n : α) ↔ 1 ≤ n := by rw [← cast_one, cast_le]
                                                -- 🎉 no goals
#align nat.one_le_cast Nat.one_le_cast

@[simp, norm_cast]
theorem cast_lt_one : (n : α) < 1 ↔ n = 0 := by
  rw [← cast_one, cast_lt, lt_succ_iff, ← bot_eq_zero, le_bot_iff]
  -- 🎉 no goals
#align nat.cast_lt_one Nat.cast_lt_one

@[simp, norm_cast]
theorem cast_le_one : (n : α) ≤ 1 ↔ n ≤ 1 := by rw [← cast_one, cast_le]
                                                -- 🎉 no goals
#align nat.cast_le_one Nat.cast_le_one

end OrderedSemiring

/-- A version of `Nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types. -/
@[simp, norm_cast]
theorem cast_tsub [CanonicallyOrderedCommSemiring α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (m n : ℕ) : ↑(m - n) = (m - n : α) := by
  cases' le_total m n with h h
  -- ⊢ ↑(m - n) = ↑m - ↑n
  · rw [tsub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    -- ⊢ ↑m ≤ ↑n
    exact mono_cast h
    -- 🎉 no goals
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    -- ⊢ ↑(m + n - n) = ↑(m + n) - ↑n
    rw [add_tsub_cancel_right, cast_add, add_tsub_cancel_right]
    -- 🎉 no goals
#align nat.cast_tsub Nat.cast_tsub

@[simp, norm_cast]
theorem cast_min [LinearOrderedSemiring α] {a b : ℕ} : ((min a b : ℕ) : α) = min (a : α) b :=
  (@mono_cast α _).map_min
#align nat.cast_min Nat.cast_min

@[simp, norm_cast]
theorem cast_max [LinearOrderedSemiring α] {a b : ℕ} : ((max a b : ℕ) : α) = max (a : α) b :=
  (@mono_cast α _).map_max
#align nat.cast_max Nat.cast_max

@[simp, norm_cast]
theorem abs_cast [LinearOrderedRing α] (a : ℕ) : |(a : α)| = a :=
  abs_of_nonneg (cast_nonneg a)
#align nat.abs_cast Nat.abs_cast

theorem coe_nat_dvd [Semiring α] {m n : ℕ} (h : m ∣ n) : (m : α) ∣ (n : α) :=
  map_dvd (Nat.castRingHom α) h
#align nat.coe_nat_dvd Nat.coe_nat_dvd

alias _root_.Dvd.dvd.natCast := coe_nat_dvd

end Nat

instance [AddMonoidWithOne α] [CharZero α] : Nontrivial α where exists_pair_ne :=
  ⟨1, 0, (Nat.cast_one (R := α) ▸ Nat.cast_ne_zero.2 (by decide))⟩
                                                         -- 🎉 no goals

section AddMonoidHomClass

variable {A B F : Type*} [AddMonoidWithOne B]

theorem ext_nat' [AddMonoid A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
  FunLike.ext f g <| by
    intro n
    -- ⊢ ↑f n = ↑g n
    induction n with
    | zero => simp_rw [Nat.zero_eq, map_zero f, map_zero g]
    | succ n ihn =>
      simp [Nat.succ_eq_add_one, h, ihn]
#align ext_nat' ext_nat'

@[ext]
theorem AddMonoidHom.ext_nat [AddMonoid A] {f g : ℕ →+ A} : f 1 = g 1 → f = g :=
  ext_nat' f g
#align add_monoid_hom.ext_nat AddMonoidHom.ext_nat

variable [AddMonoidWithOne A]

-- these versions are primed so that the `RingHomClass` versions aren't
theorem eq_natCast' [AddMonoidHomClass F ℕ A] (f : F) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by simp [map_zero f]
            -- 🎉 no goals
  | n + 1 => by rw [map_add, h1, eq_natCast' f h1 n, Nat.cast_add_one]
                -- 🎉 no goals
#align eq_nat_cast' eq_natCast'

theorem map_natCast' {A} [AddMonoidWithOne A] [AddMonoidHomClass F A B] (f : F) (h : f 1 = 1) :
    ∀ n : ℕ, f n = n
  | 0 => by simp [map_zero f]
            -- 🎉 no goals
  | n + 1 => by
    rw [Nat.cast_add, map_add, Nat.cast_add, map_natCast' f h n, Nat.cast_one, h, Nat.cast_one]
    -- 🎉 no goals
#align map_nat_cast' map_natCast'

end AddMonoidHomClass

section MonoidWithZeroHomClass

variable {A F : Type*} [MulZeroOneClass A]

/-- If two `MonoidWithZeroHom`s agree on the positive naturals they are equal. -/
theorem ext_nat'' [MonoidWithZeroHomClass F ℕ A] (f g : F) (h_pos : ∀ {n : ℕ}, 0 < n → f n = g n) :
    f = g := by
  apply FunLike.ext
  -- ⊢ ∀ (x : ℕ), ↑f x = ↑g x
  rintro (_ | n)
  -- ⊢ ↑f Nat.zero = ↑g Nat.zero
  · simp [map_zero f, map_zero g]
    -- 🎉 no goals
  · exact h_pos n.succ_pos
    -- 🎉 no goals
#align ext_nat'' ext_nat''

@[ext]
theorem MonoidWithZeroHom.ext_nat {f g : ℕ →*₀ A} : (∀ {n : ℕ}, 0 < n → f n = g n) → f = g :=
  ext_nat'' f g
#align monoid_with_zero_hom.ext_nat MonoidWithZeroHom.ext_nat

end MonoidWithZeroHomClass

section RingHomClass

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

@[simp]
theorem eq_natCast [RingHomClass F ℕ R] (f : F) : ∀ n, f n = n :=
  eq_natCast' f <| map_one f
#align eq_nat_cast eq_natCast

@[simp]
theorem map_natCast [RingHomClass F R S] (f : F) : ∀ n : ℕ, f (n : R) = n :=
  map_natCast' f <| map_one f
#align map_nat_cast map_natCast

--Porting note: new theorem
@[simp]
theorem map_ofNat [RingHomClass F R S] (f : F) (n : ℕ) [Nat.AtLeastTwo n] :
    (f (no_index (OfNat.ofNat n)) : S) = OfNat.ofNat n :=
  map_natCast f n

theorem ext_nat [RingHomClass F ℕ R] (f g : F) : f = g :=
  ext_nat' f g <| by simp only [map_one f, map_one g]
                     -- 🎉 no goals
#align ext_nat ext_nat

theorem NeZero.nat_of_injective {n : ℕ} [h : NeZero (n : R)] [RingHomClass F R S] {f : F}
    (hf : Function.Injective f) : NeZero (n : S) :=
  ⟨fun h ↦ NeZero.natCast_ne n R <| hf <| by simpa only [map_natCast, map_zero f] ⟩
                                             -- 🎉 no goals
#align ne_zero.nat_of_injective NeZero.nat_of_injective

theorem NeZero.nat_of_neZero {R S} [Semiring R] [Semiring S] {F} [RingHomClass F R S] (f : F)
    {n : ℕ} [hn : NeZero (n : S)] : NeZero (n : R) :=
  .of_map (f := f) (neZero := by simp only [map_natCast, hn])
                                 -- 🎉 no goals
#align ne_zero.nat_of_ne_zero NeZero.nat_of_neZero

end RingHomClass

namespace RingHom

/-- This is primed to match `eq_intCast'`. -/
theorem eq_natCast' {R} [NonAssocSemiring R] (f : ℕ →+* R) : f = Nat.castRingHom R :=
  RingHom.ext <| eq_natCast f
#align ring_hom.eq_nat_cast' RingHom.eq_natCast'

end RingHom

@[simp, norm_cast]
theorem Nat.cast_id (n : ℕ) : n.cast = n :=
  rfl
#align nat.cast_id Nat.cast_id

@[simp]
theorem Nat.castRingHom_nat : Nat.castRingHom ℕ = RingHom.id ℕ :=
  rfl
#align nat.cast_ring_hom_nat Nat.castRingHom_nat

/-- We don't use `RingHomClass` here, since that might cause type-class slowdown for
`Subsingleton`-/
instance Nat.uniqueRingHom {R : Type*} [NonAssocSemiring R] : Unique (ℕ →+* R) where
  default := Nat.castRingHom R
  uniq := RingHom.eq_natCast'

namespace Pi

variable {π : α → Type*} [∀ a, NatCast (π a)]

/- Porting note: manually wrote this instance.
Was `by refine_struct { .. } <;> pi_instance_derive_field` -/
instance natCast : NatCast (∀ a, π a) := { natCast := fun n _ ↦ n }

theorem nat_apply (n : ℕ) (a : α) : (n : ∀ a, π a) a = n :=
  rfl
#align pi.nat_apply Pi.nat_apply

@[simp]
theorem coe_nat (n : ℕ) : (n : ∀ a, π a) = fun _ ↦ ↑n :=
  rfl
#align pi.coe_nat Pi.coe_nat

@[simp]
theorem ofNat_apply (n : ℕ) [n.AtLeastTwo] (a : α) : (OfNat.ofNat n : ∀ a, π a) a = n := rfl

end Pi

theorem Sum.elim_natCast_natCast {α β γ : Type*} [NatCast γ] (n : ℕ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  @Sum.elim_lam_const_lam_const α β γ n
#align sum.elim_nat_cast_nat_cast Sum.elim_natCast_natCast

/-! ### Order dual -/


open OrderDual

instance [h : NatCast α] : NatCast αᵒᵈ :=
  h

instance [h : AddMonoidWithOne α] : AddMonoidWithOne αᵒᵈ :=
  h

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵒᵈ :=
  h

@[simp]
theorem toDual_natCast [NatCast α] (n : ℕ) : toDual (n : α) = n :=
  rfl
#align to_dual_nat_cast toDual_natCast

@[simp]
theorem ofDual_natCast [NatCast α] (n : ℕ) : (ofDual n : α) = n :=
  rfl
#align of_dual_nat_cast ofDual_natCast

/-! ### Lexicographic order -/


instance [h : NatCast α] : NatCast (Lex α) :=
  h

instance [h : AddMonoidWithOne α] : AddMonoidWithOne (Lex α) :=
  h

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne (Lex α) :=
  h

@[simp]
theorem toLex_natCast [NatCast α] (n : ℕ) : toLex (n : α) = n :=
  rfl
#align to_lex_nat_cast toLex_natCast

@[simp]
theorem ofLex_natCast [NatCast α] (n : ℕ) : (ofLex n : α) = n :=
  rfl
#align of_lex_nat_cast ofLex_natCast
