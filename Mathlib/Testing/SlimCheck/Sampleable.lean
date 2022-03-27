/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Mathlib.Testing.SlimCheck.Gen

structure PhantomFunction (α : Sort u) (β : Sort v) where
  f : α → β → Prop
  total : ∀ x, ∃ y, f x y
  determ : ∀ x y0 y1, f x y0 → f x y1 → y0 = y1

namespace PhantomFunction

noncomputable def eval (ph : PhantomFunction α β) (x : α) : β := Classical.choose $ ph.total x

theorem eval_eq (ph : PhantomFunction α β) : ∀ (x : α) (y : β), ph.eval x = y ↔ ph.f x y := by
  intro x y
  simp [eval]
  have h' := Classical.choose_spec <| ph.total x
  constructor <;> intro h
  next =>
    rw [h] at h'
    assumption
  next =>
    apply ph.determ x
    exact h'
    exact h

def mkPhantomFunction (g : α → β) : PhantomFunction α β where
  f x y := g x = y
  total x := ⟨_, rfl⟩
  determ x y0 y1 h0 h1 := by rw [←h0, ←h1]

def mkSizeOf (α : Type u) [inst : SizeOf α] : PhantomFunction α Nat :=
  mkPhantomFunction inst.sizeOf

class PhantomSizeOf (α : Sort u) where
  sizeOf : PhantomFunction α Nat

instance phantomSizeOf [SizeOf α] : PhantomSizeOf α where
  sizeOf := mkSizeOf α

noncomputable instance  (priority := high) sizeOfPhantom [ph : PhantomSizeOf α] : SizeOf α where
  sizeOf := ph.sizeOf.eval

theorem sizeOfPhantom_eq_SizeOf [inst : SizeOf α] : @sizeOfPhantom α (@phantomSizeOf α inst) = inst := by
  cases inst
  unfold sizeOfPhantom
  apply congrArg
  funext x
  rw [eval_eq]
  rfl

end PhantomFunction

namespace SlimCheck

open Random Gen PhantomFunction

abbrev ShrinkFn (α : Type u) [PhantomSizeOf α] := (x : α) → List { y : α // sizeOfPhantom.sizeOf y < sizeOfPhantom.sizeOf x }

class Sampleable (α : Type u) [Repr α] where
  sample {} : Gen α

class Shrinkable (α : Type u) [phSz : PhantomSizeOf α] where
  shrink : @ShrinkFn α phSz := λ _ => []

class SampleableExt (α : Sort u) where
  proxy : Type v
  [phSz : PhantomSizeOf proxy]
  [proxyRepr : Repr proxy]
  [samp : Sampleable proxy]
  [shrink : Shrinkable proxy]
  interp : proxy → α

attribute [instance] SampleableExt.samp
attribute [instance] SampleableExt.proxyRepr
attribute [instance] SampleableExt.shrink
attribute [instance] SampleableExt.phSz

namespace SampleableExt

def sample (α : Type u) [SampleableExt α] : Gen (SampleableExt.proxy α) := SampleableExt.samp.sample

instance ofSampleable [Repr α] [Sampleable α] [sz : SizeOf α] [PhantomSizeOf α] [Shrinkable α] : SampleableExt α where
  proxy := α 
  phSz := inferInstance
  proxyRepr := inferInstance
  samp := inferInstance
  shrink := inferInstance
  interp := id

end SampleableExt

section Samplers

instance Nat.sampleable : Sampleable Nat where
  sample := do choose Nat 0 (←getSize) (Nat.zero_le _)

instance Fin.sampleable {n : Nat} : Sampleable (Fin (n.succ)) where
  sample := do choose (Fin n.succ) (Fin.ofNat 0) (Fin.ofNat (←getSize)) (by
    simp [Fin.ofNat, LE.le]
    exact Nat.zero_le _
  )

instance Int.sampleable : Sampleable Int where
  sample := do choose Int (-(←getSize)) (←getSize) (le_trans (Int.neg_nonpos_of_nonneg (Int.ofNat_zero_le _)) (Int.ofNat_zero_le _))

instance Bool.sampleable : Sampleable Bool where
  sample := chooseAny Bool

def Char.sampleable (length : Nat) (chars : List Char) (pos : 0 < chars.length) : Sampleable Char :=
  {
    sample := do
      let x ← choose Nat 0 length (Nat.zero_le _)
      if x.val == 0 then
        let n ← Sampleable.sample Nat
        pure $ Char.ofNat n
      else
        elements chars pos
  }

instance Char.sampleableDefault : Sampleable Char :=
  Char.sampleable 3 " 0123abcABC:,;`\\/".toList (by decide)

instance Prod.sampleable [Repr α] [Repr β] [Sampleable α] [Sampleable β] : Sampleable (Prod α β) where
  sample := prodOf (Sampleable.sample α) (Sampleable.sample β)

end Samplers

section Shrinkers

def Nat.shrink (n : Nat) : List { y : Nat // sizeOfPhantom.sizeOf y < sizeOfPhantom.sizeOf n } :=
  if h : 0 < n then
    let m := n/2
    have h : m < n := by
      apply Nat.div_lt_self h
      decide
    let rest := shrink m
    let current := ⟨m, by rw [sizeOfPhantom_eq_SizeOf]; exact h⟩
    current ::
      rest.map (λ x => {x with property := by
        let h2 := x.property
        simp [sizeOfPhantom_eq_SizeOf]
        simp [sizeOfPhantom_eq_SizeOf] at h2
        exact Nat.lt_trans h2 h
      })
  else
    []

instance Nat.shrinkable : Shrinkable Nat where
  shrink := Nat.shrink

def Fin.shrink {n : Nat} (m : Fin n.succ) : List { y : Fin n.succ // sizeOfPhantom.sizeOf y < sizeOfPhantom.sizeOf m } :=
  let shrinks := Nat.shrink m.val
  shrinks.map (λ x => {x with property := sorry})

instance Fin.shrinkable {n : Nat} : Shrinkable (Fin n.succ) where
  shrink := Fin.shrink

abbrev Int.sizeOfAbs : SizeOf Int := ⟨Int.natAbs⟩

attribute [local instance] Int.sizeOfAbs

def Int.shrink (n : Int) : List { y : Int // sizeOfPhantom.sizeOf y < sizeOfPhantom.sizeOf n } :=
  Nat.shrink n.natAbs |>.map λ ⟨x, h⟩ => ⟨-x, (by rw [sizeOfPhantom_eq_SizeOf] at *; simp only [SizeOf.sizeOf]; rw [Int.natAbs_neg]; exact h)⟩

instance Int.shrinkable : Shrinkable Int where
  shrink := Int.shrink

instance Bool.shrinkable : Shrinkable Bool := {}

def Prod.shrink [SizeOf α] [SizeOf β] [shrA : Shrinkable α] [shrB : Shrinkable β] : ShrinkFn (α × β) := λ (fst, snd) =>
  let shrink1 := shrA.shrink fst |>.map fun ⟨x, _⟩ => ⟨(x, snd), by rw [sizeOfPhantom_eq_SizeOf] at *; simp_all_arith⟩
  let shrink2 := shrB.shrink snd |>.map fun ⟨x, _⟩ => ⟨(fst, x), by rw [sizeOfPhantom_eq_SizeOf] at *; simp_all_arith⟩
  shrink1 ++ shrink2

instance Prod.shrinkable [SizeOf α] [SizeOf β] [Shrinkable α] [Shrinkable β] : Shrinkable (Prod α β) where
  shrink := Prod.shrink

instance Prop.sampleableExt : SampleableExt Prop where
  proxy := Bool
  phSz := inferInstance
  samp := inferInstance
  shrink := inferInstance
  interp := Coe.coe

end Shrinkers

def NoShrink (α : Type u) := α

namespace NoShrink

def mk (x : α) : NoShrink α := x
def get (x : NoShrink α) : α := x

instance inhabited [inst : Inhabited α] : Inhabited (NoShrink α) := inst
instance repr [inst : Repr α] : Repr (NoShrink α) := inst

instance sampleable [Repr α] [Sampleable α] : Sampleable (NoShrink α) where
  sample := NoShrink.mk <$> Sampleable.sample α

instance shrinkable : Shrinkable (NoShrink α) where
  shrink := λ _ => []

end NoShrink

instance String.sampleable : Sampleable String where
  sample := do
    let xs ← listOf $ Sampleable.sample Char
    pure xs.asString

end SlimCheck
