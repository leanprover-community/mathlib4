import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Vector

#check Vector.mapAccumr

/-!
  A `Bitvec n` is morally a sequence of `n` bits.
  This file establishes a way to shift to this perspective by proving the equivalence between
  `Bitvec n` and `Vector bool n`.
  Furthermore, we show how various (arithmetic) operations on bitvectors relate to a naive
  bit-by-bit implementation of those operations using the vector perspective.
-/

namespace BitVec

variable {n : Nat}
universe u v

/-
  ## Pseudo constructors
-/

/-- The empty bitvector -/
def nil : BitVec 0 :=
  BitVec.zero 0

/-- Prepend a single bit to the front of a bitvector. The new bit is the most significant bit -/
def cons (x : Bool) (xs : BitVec n) : BitVec (n+1) :=
  ⟨Nat.bit x xs.val, by
    simp only [Nat.bit, cond, bit1, bit0]
    have : xs.val < 2 ^ n := xs.prop
    cases x <;> simp only
    . sorry
    . sorry
  ⟩

/-- Append a single bit to the end of a bitvector. The new bit is the least significant bit -/
def concat (xs : BitVec n) (x : Bool) : BitVec (n+1) :=
  let ys : BitVec 1 := if x then
      ⟨1, by decide⟩
    else
      BitVec.zero _
  xs.append ys

/-- There is only one `empty` bitvector, namely, `nil` -/
theorem zero_length_eq_nil :
    ∀ (xs : BitVec 0), xs = nil := by
  sorry

/-!
  ## Induction principles
-/

/-- A custom recursion principle for bitvectors in terms of `nil` and `cons` -/
@[elab_as_elim]
def consRecursion {motive : {n : Nat} → BitVec n → Sort u}
    (nil : motive nil)
    (cons : {n : Nat} → (x : Bool) → (xs : BitVec n) → motive xs → motive (cons x xs))
    {n : Nat} (xs : BitVec n) : motive xs :=
  /-
    This one might be a bit hard to prove.
    For now, the `consRecursion_nil` and `consRecursion_cons` theorems fully specify how
    `consRecursion` should behave, and it is enough to use those in proofs about definitions using
    `consRecursion`
  -/
  sorry

@[simp]
theorem consRecursion_nil {motive nil cons} :
    consRecursion (motive:=motive) nil cons .nil = nil := by
  sorry

@[simp]
theorem consRecursion_cons {motive nil cons} {x : Bool} {xs : BitVec n} :
    consRecursion (motive:=motive) nil cons (.cons x xs)
    = cons x xs (consRecursion nil cons xs) := by
  sorry

/-
  `consRecursion` is a so-called custom recursion principle, which allows us to pretend that
  `BitVec` is almost an inductive type, with `nil` and `cons` as its constructors.

  For example, in proofs (using tactic mode) about some `xs : BitVec n`, we can write
  ```lean
  induction xs using BitVec.consRecursion
  ```
  And the goal would be split in two cases, one for `nil` and one for `cons`, with an induction
  hypothesis for the second goal.

  This is why recursion principles are also sometimes called induction principles.
  However, they are also useful beyond proofs. A recursion principle can be used to define a
  structurally recursive function on bitvectors.
  That is, in `let f := consRecursion h_nil h_cons`, the `h_nil` argument gives the return value of
  `f BitVec.nil`, while `h_cons` is a function that maps `x`, `xs` and `f xs` to the return value of
  `f (BitVec.cons x xs)`
-/


/-!
  ## Equivalence
-/

/-- Turn a bitvector into a vector of bools of the same length -/
def asVector : BitVec n → Vector Bool n :=
  sorry

/-- Turn a vector of bools into a bitvector of the same length -/
def ofVector : Vector Bool n → BitVec n :=
  sorry

def vectorEquiv : BitVec n ≃ Vector Bool n where
  toFun := asVector
  invFun := ofVector
  left_inv := sorry
  right_inv := sorry

variable {x y : BitVec n} {m : Nat}

/-!
  ## Constants
-/

theorem zero_asVector :
    (BitVec.zero n).asVector = Vector.replicate n false := by
  sorry

theorem negOne_asVector :
    (-1 : BitVec n).asVector = Vector.replicate n true := by
  sorry

theorem one_asVector :
    (1 : BitVec n).asVector = match n with
      | 0 => sorry
      | n+1 => Vector.snoc (.zero n) true := by
  sorry

/-!
  ## Bitwise
-/

theorem complement_asVector :
    (~~~x) = (ofVector <| Vector.map not x.asVector) := by
  sorry

theorem and_asVector :
    (x &&& y) = (ofVector <| Vector.map₂ and x.asVector y.asVector) := by
  sorry

theorem or_asVector :
    (x ||| y) = (ofVector <| Vector.map₂ or x.asVector y.asVector) := by
  sorry

theorem xor_asVector :
    (x ^^^ y) = (ofVector <| Vector.map₂ xor x.asVector y.asVector) := by
  sorry

/-
  TODO: `shiftLeft`, `shiftRight`, `rotateLeft`, `rotateRight`
-/

/-!
  ## Comparisons
-/

/-
  TODO: `lt`, `le`, `slt`, `sle`, `sgt`, `sge`
-/

/-!
  ## Arithmetic
-/

theorem add_asVector :
    x + y = (ofVector <| Prod.snd <|
      Vector.mapAccumr₂ (fun x y c => (_, _)) x.asVector y.asVector false
    ) := by
  sorry

theorem sub_asVector :
    x - y = (ofVector <| Prod.snd <|
      Vector.mapAccumr₂ (fun x y c => (_, _)) x.asVector y.asVector false
    ) := by
  sorry

/-
  TODO: `mul`, `div`, `mod`
  These operations cannot (easily) be defined in terms of `mapAccumr`.
  We could still formulate bitwise implementatoins, but the question is whether this is even useful
-/

end BitVec
