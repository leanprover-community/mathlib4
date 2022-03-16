/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Mathlib.Testing.SlimCheck.Gen
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Find

namespace SlimCheck

open Random

structure ShrinkFn (α : Type u) [sz : SizeOf α] where
  run : (x : α) → List { y : α // sz.sizeOf y < sz.sizeOf x }

class Sampleable (α : Type u) where
  sample : Gen α

class Shrinkable (α : Type u) [wf : SizeOf α] where
  shrink : @ShrinkFn α wf

class SampleableExt (α : Sort u) where
  proxyRepr : Type v
  [samp : Sampleable proxyRepr]
  [shrink : Shrinkable proxyRepr]
  interp : proxyRepr → α

attribute [instance] SampleableExt.samp

section GenericSampleableInstances

instance (priority := low) [Sampleable α] [SizeOf α] : Shrinkable α where
  shrink := ⟨λ _ => []⟩

instance SampleableExt.ofSampleable {α : Type u} [Sampleable α] [Shrinkable α] [SizeOf α] : SampleableExt α where
  proxyRepr := α 
  samp := inferInstance
  shrink := inferInstance
  interp := id

end GenericSampleableInstances

section Shrinkers

def Nat.shrink (n : Nat) : List { y : Nat // sizeOf y < sizeOf n } :=
  if h : 0 < n then
    let m := n/2
    have h : m < n := by
      apply Nat.div_lt_self h
      decide
    let rest := shrink m
    ⟨m, h⟩ :: rest.map (λ x => {x with property := Nat.lt_trans x.property h})
  else
    []

instance Nat.sampleable : Sampleable Nat where
  sample := do choose Nat 0 (←getSize) (Nat.zero_le _)

instance Nat.shrinkable : Shrinkable Nat where
  shrink := ⟨Nat.shrink⟩

def Fin.shrink {n : Nat} (m : Fin n.succ) : List { y : Fin n.succ // sizeOf y < sizeOf m } :=
  let shrinks := Nat.shrink m.val
  shrinks.map (λ x => {x with property := sorry})

instance Fin.sampleable {n : Nat} : Sampleable (Fin (n.succ)) where
  sample := do choose (Fin n.succ) (Fin.ofNat 0) (Fin.ofNat (←getSize)) (by
    simp [Fin.ofNat, LE.le]
    exact Nat.zero_le _
  )

instance Fin.shrinkable {n : Nat} : Shrinkable (Fin n.succ) where
  shrink := ⟨Fin.shrink⟩

abbrev Int.sizeOfAbs : SizeOf Int := ⟨Int.natAbs⟩

attribute [local instance] Int.sizeOfAbs

def Int.shrink (n : Int) : List { y : Int // sizeOfAbs.sizeOf y < sizeOfAbs.sizeOf n } :=
  Nat.shrink n.natAbs |>.map λ ⟨x, h⟩ => ⟨-x, (by simp only [SizeOf.sizeOf]; rw [Int.natAbs_neg]; exact h)⟩

instance Int.sampleable : Sampleable Int where
  sample := do choose Int (-(←getSize)) (←getSize) (le_trans (Int.neg_nonpos_of_nonneg (Int.ofNat_zero_le _)) (Int.ofNat_zero_le _))

instance Int.shrinkable : Shrinkable Int where
  shrink := ⟨Int.shrink⟩

instance Bool.sampleable : Sampleable Bool where
  sample := chooseAny Bool

def Prod.shrink [SizeOf α] [SizeOf β] (shrA : ShrinkFn α) (shrB : ShrinkFn β) : ShrinkFn (α × β) := ⟨λ (fst, snd) =>
  let shrink1 := shrA.run fst |>.map fun ⟨x, _⟩ => ⟨(x, snd), by simp_all_arith⟩
  let shrink2 := shrB.run snd |>.map fun ⟨x, _⟩ => ⟨(fst, x), by simp_all_arith⟩
  shrink1 ++ shrink2⟩

instance Prod.sampleable [Sampleable α] [Sampleable β] : Sampleable (Prod α β) where
  sample := prodOf Sampleable.sample Sampleable.sample

instance Prod.shrinkable [SizeOf α] [SizeOf β] [Shrinkable α] [Shrinkable β] : Shrinkable (Prod α β) where
  shrink := Prod.shrink Shrinkable.shrink Shrinkable.shrink

def Char.sampleable (length : Nat) (chars : List Char) (pos : 0 < chars.length) : Sampleable Char :=
  {
    sample := do
      let x ← choose Nat 0 length (Nat.zero_le _)
      if x.val == 0 then
        let n ← Sampleable.sample
        pure $ Char.ofNat n
      else
        elements chars pos
  }

instance Char.sampleableDefault : Sampleable Char :=
  Char.sampleable 3 " 0123abcABC:,;`\\/".toList (by decide)

section ListShrink

variable {α : Type u} [SizeOf α] (shr : ShrinkFn α)
-- TODO: List shrinker

end ListShrink
end Shrinkers

instance Prop.sampleableExt : SampleableExt Prop where
  proxyRepr := Bool 
  samp := inferInstance
  shrink := inferInstance
  interp := Coe.coe

def NoShrink (α : Type u) := α

namespace NoShrink

def mk (x : α) : NoShrink α := x
def get (x : NoShrink α) : α := x

instance inhabited [Inhabited α] : Inhabited (NoShrink α) := ⟨(default : α)⟩

instance sampleable [Sampleable α] : Sampleable (NoShrink α) where
  sample := NoShrink.mk <$> Sampleable.sample

instance shrinkable : Shrinkable α where
  shrink := ⟨λ _ => []⟩

end NoShrink

instance String.sampleable : Sampleable String where
  sample := do
    let xs ← listOf Sampleable.sample
    pure xs.asString

instance String.shrinkable : Shrinkable String where
  shrink := sorry -- requires List.shrinkable

end SlimCheck
