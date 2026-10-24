/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Order.SymmDiff
public import Mathlib.Tactic.Simps.Basic

import Mathlib.Tactic.TermCongr

/-!
# A type synonym to induce an order lattice from bitwise operators

This file provides the `BitwiseOrder` type synonym, which induces lattice and Boolean algebra
structures on types equipped with bitwise operations:

* `a ≤ b` is defined as `a &&& b = a`
* `a ⊓ b` is implemented as `a &&& b`
* `a ⊔ b` is implemented as `a ||| b`
* `a \ b` is implemented as `a ^^^ (a &&& b)`
* `a ∆ b` (`symmDiff`) is equal to `a ^^^ b`
* `aᶜ` is implemented as `~~~a`

To avoid duplicating order-theoretic proofs across `Nat`, `BitVec w`, `UInt8`, etc., this file
defines a hierarchy of `Prop`-valued lawfulness typeclasses on the underlying type `α`:

* `IsDistribBitwiseLattice α`: laws on `&&&` and `|||` inducing `DistribLattice (BitwiseOrder α)`
* `IsGeneralizedBitwiseAlgebra α`: extends `IsDistribBitwiseLattice α` and `LawfulXor α` with laws
  on `^^^`, inducing `GeneralizedBooleanAlgebra (BitwiseOrder α)` (e.g. for `Nat`)
* `IsBitwiseAlgebra α`: extends `IsGeneralizedBitwiseAlgebra α` with complement laws on `~~~`,
  inducing `BooleanAlgebra (BitwiseOrder α)` (e.g. for `BitVec w` and `UInt*`)

Notably `BitwiseOrder Nat` is an efficient implementation of `Finset ℕ`, and
`BitwiseOrder (BitVec w)` is an efficient implementation of `Finset (Fin w)`.

TODO: provide the order isomorphism between these types.
-/

@[expose] public section

section lawfulness_classes

/-- A typeclass asserting that `&&&` and `|||` satisfy the distributive and absorption laws needed
to induce a `DistribLattice` structure on `BitwiseOrder α`. -/
class IsDistribBitwiseLattice (α : Type*) [AndOp α] [OrOp α] : Prop where
  [toIdempotentOp_and : Std.IdempotentOp (α := α) HAnd.hAnd]
  [toAssociative_and : Std.Associative (α := α) HAnd.hAnd]
  [toCommutative_and : Std.Commutative (α := α) HAnd.hAnd]
  and_or_distrib_left (x y z : α) : x &&& (y ||| z) = (x &&& y) ||| (x &&& z)
  and_or_self_left (x y : α) : x &&& (x ||| y) = x
  and_or_self_right (x y : α) : y &&& (x ||| y) = y

namespace IsDistribBitwiseLattice
variable {α : Type*} [AndOp α] [OrOp α] [IsDistribBitwiseLattice α]

attribute [instance] toIdempotentOp_and toAssociative_and toCommutative_and

theorem and_or_distrib_right (x y z : α) : (x ||| y) &&& z = (x &&& z) ||| (y &&& z) := by
  simp only [Std.Commutative.comm (op := HAnd.hAnd) _ z, and_or_distrib_left]

attribute [grind =] and_or_distrib_left and_or_distrib_right and_or_self_left and_or_self_right

end IsDistribBitwiseLattice

/-- A typeclass asserting that `&&&`, `|||`, and `^^^` satisfy the laws needed to induce a
`GeneralizedBooleanAlgebra` structure on `BitwiseOrder α`, with relative complement `a \ b` given by
`a ^^^ (a &&& b)`. -/
class IsGeneralizedBitwiseAlgebra (α : Type*) [AndOp α] [OrOp α] [XorOp α] [Zero α] : Prop extends
    IsDistribBitwiseLattice α, LawfulXor α where
  and_xor_distrib_left (x y z : α) : x &&& (y ^^^ z) = (x &&& y) ^^^ (x &&& z)
  or_xor_self (x y : α) : x ||| (y ^^^ x) = x ||| y

namespace IsGeneralizedBitwiseAlgebra
variable {α : Type*} [AndOp α] [OrOp α] [XorOp α] [Zero α] [IsGeneralizedBitwiseAlgebra α]

theorem and_xor_distrib_right (x y z : α) :
    (x ^^^ y) &&& z = (x &&& z) ^^^ (y &&& z) := by
  simp only [Std.Commutative.comm (op := HAnd.hAnd) _ z, and_xor_distrib_left]

attribute [grind =] and_xor_distrib_left and_xor_distrib_right or_xor_self LawfulXor.xor_self

theorem bot_eq_zero {bot : α} [Std.LawfulIdentity (α := α) (· ||| ·) bot] : bot = 0 := by
  have := IsDistribBitwiseLattice.and_or_self_left bot 0
  have := Std.LawfulLeftIdentity.left_id (op := (· ||| ·)) (0 : α)
  have := LawfulXor.xor_self bot
  grind

end IsGeneralizedBitwiseAlgebra

instance : IsGeneralizedBitwiseAlgebra Nat where
  and_or_distrib_left := Nat.and_or_distrib_left
  and_or_self_left _ _ := by apply Nat.eq_of_testBit_eq; grind
  and_or_self_right _ _ := by apply Nat.eq_of_testBit_eq; grind
  and_xor_distrib_left _ _ _ := Nat.and_xor_distrib_left
  or_xor_self _ _ := by apply Nat.eq_of_testBit_eq; grind

/-- A typeclass asserting that `&&&`, `|||`, `^^^`, and `~~~` satisfy the laws needed to induce a
`BooleanAlgebra` structure on `BitwiseOrder α`. -/
class IsBitwiseAlgebra (α : Type*)
    {bot top : outParam α} [AndOp α] [OrOp α] [XorOp α] [Zero α] [Complement α]
    [Std.LawfulIdentity (α := α) (· ||| ·) bot] [Std.LawfulIdentity (α := α) (· &&& ·) top] :
    Prop extends IsGeneralizedBitwiseAlgebra α where
  and_not_self (x : α) : x &&& ~~~x = bot
  or_not_self (x : α) : x ||| ~~~x = top

attribute [simp, grind =] IsBitwiseAlgebra.and_not_self IsBitwiseAlgebra.or_not_self

instance {w} : IsBitwiseAlgebra (BitVec w) where
  and_or_distrib_left := by grind
  and_or_self_left := by grind
  and_or_self_right := by grind
  and_xor_distrib_left := by grind
  or_xor_self := by grind
  and_not_self := BitVec.and_not_self
  or_not_self := BitVec.or_not_self

open Lean in
run_cmd do
  for t in [`UInt8, `UInt16, `UInt32, `UInt64, `USize] do
    let ty := mkIdent t
    let and_not_self := mkIdent (t ++ `and_not_self)
    let or_not_self := mkIdent (t ++ `or_not_self)
    Elab.Command.elabCommand <| ← `(
      namespace $ty
      instance : IsBitwiseAlgebra $ty where
        and_or_distrib_left := by grind
        and_or_self_left := by grind
        and_or_self_right := by grind
        and_xor_distrib_left := by grind
        or_xor_self := by grind
        and_not_self _ := $and_not_self
        or_not_self _ := $or_not_self
      end $ty
    )

end lawfulness_classes

/-- `BitwiseOrder α` is a synonym for `α` that induces a lattice structure from bitwise operators.

It is typically instantiated with `α := Nat` or `α := BitVec w`.
-/
@[ext, grind]
structure BitwiseOrder (α : Type*) where ofBits ::
  /-- The representation as bits. -/
  bits : α

namespace BitwiseOrder
variable {α : Type*}

instance [AndOp α] : LE (BitwiseOrder α) where
  le a b := (a.bits &&& b.bits) = a.bits

@[simp, grind .]
theorem ofBits_le_ofBits [AndOp α] {a b : α} :
    ofBits a ≤ ofBits b ↔ a &&& b = a := Iff.rfl

instance [AndOp α] [DecidableEq α] : DecidableLE (BitwiseOrder α) :=
  fun _ _ => decidable_of_iff' _ ofBits_le_ofBits

instance [AndOp α] : Min (BitwiseOrder α) where
  min a b := ⟨a.bits &&& b.bits⟩

@[simp, grind =]
theorem bits_inf [AndOp α] {a b : BitwiseOrder α} : (a ⊓ b).bits = a.bits &&& b.bits := rfl

@[simp, grind =]
theorem ofBits_inf_ofBits [AndOp α] {a b : α} : ofBits a ⊓ ofBits b = ofBits (a &&& b) := rfl

section sup
variable [OrOp α]

instance : Max (BitwiseOrder α) where
  max a b := ⟨a.bits ||| b.bits⟩

@[simp, grind =]
theorem bits_sup {a b : BitwiseOrder α} : (a ⊔ b).bits = a.bits ||| b.bits := rfl

@[simp, grind =]
theorem ofBits_sup_ofBits {a b : α} : ofBits a ⊔ ofBits b = ofBits (a ||| b) := rfl

end sup

section compl
variable [Complement α]

instance : Compl (BitwiseOrder α) where
  compl a := ⟨~~~a.bits⟩

@[simp, grind =]
theorem bits_compl {a : BitwiseOrder α} : aᶜ.bits = ~~~a.bits := rfl

@[simp, grind =]
theorem ofBits_compl {a : α} : (ofBits a)ᶜ = ofBits (~~~a) := rfl

end compl

section sdiff
variable [AndOp α] [XorOp α]

instance : SDiff (BitwiseOrder α) where
  sdiff a b := ⟨a.bits ^^^ (a.bits &&& b.bits)⟩

@[simp, grind =]
theorem bits_sdiff {a b : BitwiseOrder α} : (a \ b).bits = a.bits ^^^ (a.bits &&& b.bits) := rfl

@[simp, grind =]
theorem ofBits_sdiff_ofBits {a b : α} :
    ofBits a \ ofBits b = ofBits (a ^^^ (a &&& b)) := rfl

end sdiff

section SemilatticeInf
variable [AndOp α] [Std.IdempotentOp (α := α) HAnd.hAnd] [Std.Associative (α := α) HAnd.hAnd]

instance : Preorder (BitwiseOrder α) where
  le_refl a := by grind
  le_trans a b c (hab : _ = _) (hbc : _ = _) := by grind

variable [Std.Commutative (α := α) HAnd.hAnd]

instance : SemilatticeInf (BitwiseOrder α) where
  le_antisymm a b (hab : _ = _) (hba : _ = _) := by grind
  inf := Min.min
  inf_le_left a b := by grind
  inf_le_right a b := by grind
  le_inf a b := by grind

end SemilatticeInf

@[simps]
instance {top : α} [AndOp α] [Std.LawfulIdentity (α := α) (· &&& ·) top] :
    OrderTop (BitwiseOrder α) where
  top := ⟨top⟩
  le_top a := Std.LawfulRightIdentity.right_id a.bits

section DistribLattice
variable [AndOp α] [OrOp α]

instance [IsDistribBitwiseLattice α] : Lattice (BitwiseOrder α) where
  sup := Max.max
  le_sup_left a b := by
    change _ = _
    simp
    grind
  le_sup_right a b := by
    change _ = _
    simp
    grind
  sup_le a b c (ha : _ = _) (hb : _ = _) := private
    (IsDistribBitwiseLattice.and_or_distrib_right _ _ _).trans congr($ha ||| $hb)

instance [IsDistribBitwiseLattice α] : DistribLattice (BitwiseOrder α) :=
  .ofInfSupLe fun a b c => by
    change _ = _
    simp
    grind

@[simps]
instance {bot : α} [IsDistribBitwiseLattice α]
    [Std.LawfulIdentity (α := α) (· ||| ·) bot] : OrderBot (BitwiseOrder α) where
  bot := ⟨bot⟩
  bot_le a := private
    congr(bot &&& $(Std.LawfulLeftIdentity.left_id (op := (· ||| ·)) a.bits) = bot).mp
      (le_sup_left (a := ⟨bot⟩) (b := a))

attribute [grind =] bot_bits top_bits

instance {bot top : α} [IsDistribBitwiseLattice α]
    [Std.LawfulIdentity (α := α) (· ||| ·) bot] [Std.LawfulIdentity (α := α) (· &&& ·) top] :
    BoundedOrder (BitwiseOrder α) where

end DistribLattice

instance {bot : α} [AndOp α] [OrOp α] [XorOp α] [Zero α] [IsGeneralizedBitwiseAlgebra α]
    [Std.LawfulIdentity (α := α) (· ||| ·) bot] :
    GeneralizedBooleanAlgebra (BitwiseOrder α) where
  sup_inf_sdiff a b := by
    ext
    simp only [bits_sup, bits_inf, bits_sdiff, IsGeneralizedBitwiseAlgebra.or_xor_self]
    exact congrArg bits ((sup_comm (a ⊓ b) a).trans sup_inf_self)
  inf_inf_sdiff a b := by
    ext
    simp [IsGeneralizedBitwiseAlgebra.bot_eq_zero]
    grind

open scoped symmDiff in
@[simp, grind =]
theorem bits_symmDiff [AndOp α] [OrOp α] [XorOp α] [Zero α] [IsGeneralizedBitwiseAlgebra α]
    {a b : BitwiseOrder α} : (a ∆ b).bits = a.bits ^^^ b.bits := by
  have hza (x y : BitwiseOrder α) : ofBits (x.bits ^^^ y.bits) ⊓ x = x \ y := by ext; simp; grind
  have hzb : ofBits (a.bits ^^^ b.bits) ⊓ b = b \ a := by rw [LawfulXor.xor_comm]; exact hza b a
  have hzb_sup : b ⊔ ofBits (a.bits ^^^ b.bits) = b ⊔ a := by
    ext; simp [IsGeneralizedBitwiseAlgebra.or_xor_self]
  suffices a ∆ b = ofBits (a.bits ^^^ b.bits) from congrArg bits this
  rw [symmDiff_def, ← hza, ← hzb, ← inf_sup_left, sup_comm a b, ← hzb_sup, sup_comm b, inf_sup_self]

open scoped symmDiff in
@[simp, grind =]
theorem ofBits_symmDiff_ofBits [AndOp α] [OrOp α] [XorOp α] [Zero α]
    [IsGeneralizedBitwiseAlgebra α] {a b : α} :
    ofBits a ∆ ofBits b = ofBits (a ^^^ b) := by
  ext
  simp

instance {bot top : α}
    [AndOp α] [OrOp α] [XorOp α] [Zero α] [Complement α]
    [Std.LawfulIdentity (α := α) (· ||| ·) bot]
    [Std.LawfulIdentity (α := α) (· &&& ·) top] [IsBitwiseAlgebra α] :
    BooleanAlgebra (BitwiseOrder α) where
  __ : BoundedOrder (BitwiseOrder α) := inferInstance
  __ : GeneralizedBooleanAlgebra (BitwiseOrder α) := inferInstance
  inf_compl_le_bot a := by
    change _ = _
    grind
  top_le_sup_compl a := by
    change _ = _
    grind
  sdiff_eq x y := by
    have htop : y ⊔ yᶜ = ⊤ := by ext; simp
    have hbot : y ⊓ yᶜ = ⊥ := by ext; simp
    refine sdiff_unique ?_ ?_
    · rw [← inf_sup_left, htop, inf_top_eq]
    · rw [← inf_inf_distrib_left, hbot, inf_bot_eq]

example : GeneralizedBooleanAlgebra (BitwiseOrder Nat) := by infer_instance
example : BooleanAlgebra (BitwiseOrder UInt8) := by infer_instance
example : BooleanAlgebra (BitwiseOrder UInt16) := by infer_instance
example : BooleanAlgebra (BitwiseOrder UInt32) := by infer_instance
example : BooleanAlgebra (BitwiseOrder UInt64) := by infer_instance
example : BooleanAlgebra (BitwiseOrder USize) := by infer_instance
example {n} : BooleanAlgebra (BitwiseOrder (BitVec n)) := by infer_instance

end BitwiseOrder
