/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Mathlib.Testing.SlimCheck.Gen
/-!
# `Sampleable` Class
This class permits the creation samples of a given type
controlling the size of those values using the `Gen` monad`.

# `Shrinkable` Class
This class helps minimize examples by creating smaller versions of
given values.

When testing a proposition like `∀ n : ℕ, prime n → n ≤ 100`,
`SlimCheck` requires that `ℕ` have an instance of `Sampleable` and for
`prime n` to be decidable.  `SlimCheck will then use the instance of
`Sampleable` to generate small examples of ℕ and progressively increase
in size. For each example `n`, `prime n` is tested. If it is false,
the example will be rejected (not a test success nor a failure) and
`SlimCheck` will move on to other examples. If `prime n` is true, `n
≤ 100` will be tested. If it is false, `n` is a counter-example of `∀
n : ℕ, prime n → n ≤ 100` and the test fails. If `n ≤ 100` is true,
the test passes and `SlimCheck` moves on to trying more examples.

This is a port of the Haskell QuickCheck library.

## Main definitions
  * `Sampleable` class
  * `Shrinkable` class
  * `SampleableExt` class

### `Sampleable`
`Sampleable α` provides ways of creating examples of type `α`,

### `Shrinkable
Given an example `x : α`, `Shrinkable α` gives us a way to shrink it
and suggest simpler examples.

### `SampleableExt`
`SampleableExt` generalizes the behavior of `Sampleable` and `Shrinkable`
and makes it possible to express instances for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.
For that purpose, `SampleableExt` provides a proxy representation
`proxy` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type.

## Shrinking
Shrinking happens when `SlimCheck` find a counter-example to a
property.  It is likely that the example will be more complicated than
necessary so `SlimCheck` proceeds to shrink it as much as
possible. Although equally valid, a smaller counter-example is easier
for a user to understand and use.

The `Shrinkable` class, , has a `shrink` function so that we can use
specialized knowledge while shrinking a value. It is not responsible
for the whole shrinking process however. It only has to take one step
in the shrinking process. `SlimCheck` will repeatedly call `shrink`
until no more steps can be taken. Because `shrink` guarantees that the
size of the candidates it produces is strictly smaller than the
argument, we know that `SlimCheck` is guaranteed to terminate.

## Tags

random testing

## References
  * https://hackage.haskell.org/package/QuickCheck
-/

/-- This structure allows us to hide functions (especially noncomputable
ones) in `Prop`, thus not requiring the compiler to generate any code
for them. This is interesting if you have (noncomputable) functions
you want to store in datatypes for proofs but not have generated any
code for since they are not used.
-/
structure PhantomFunction (α : Sort u) (β : Sort v) where
  f : α → β → Prop
  total : ∀ x, ∃ y, f x y
  determ : ∀ x y0 y1, f x y0 → f x y1 → y0 = y1

namespace PhantomFunction

/-- Evaluate the function hidden inside `ph`. -/
noncomputable def eval (ph : PhantomFunction α β) (x : α) : β := Classical.choose $ ph.total x

/-- Evaluating the function hidden inside a `PhantomFunction` is equivalent
to evaluating the original function. -/
@[simp]
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

/-- Hide a regular function inside a `PhantomFunction`. -/
def mkPhantomFunction (g : α → β) : PhantomFunction α β where
  f x y := g x = y
  total x := ⟨_, rfl⟩
  determ x y0 y1 h0 h1 := by rw [←h0, ←h1]

/-- A specialized `mkPhantomFunction` for `SizeOf` instances. -/
def mkSizeOf (α : Type u) [inst : SizeOf α] : PhantomFunction α Nat :=
  mkPhantomFunction inst.sizeOf

/-- A typeclass to contain `SizeOf` instances hidden inside a `PhantomFunction`
unlike the auto generated `SizeOf` instances this one can be stored
in datatypes for proof purposes. -/
class PhantomSizeOf (α : Sort u) where
  phSizeOf : PhantomFunction α Nat

instance phantomSizeOf [SizeOf α] : PhantomSizeOf α where
  phSizeOf := mkSizeOf α

noncomputable instance sizeOfPhantom [ph : PhantomSizeOf α] : SizeOf α where
  sizeOf := ph.phSizeOf.eval

/-- A specialized `eval_eq` for `SizeOf` instances. -/
@[simp]
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

/-- `ShrinkFn α` is the type of functions that shrink an argument of type `α` -/
abbrev ShrinkFn (α : Type u) [PhantomSizeOf α] := (x : α) → List { y : α // sizeOfPhantom.sizeOf y < sizeOfPhantom.sizeOf x }

/-- `Sampleable α` provides ways of creating examples of type `α`. -/
class Sampleable (α : Type u) [Repr α] where
  sample {} : Gen α

/-- Given an example `x : α`, `Shrinkable α` gives us a way to shrink it
and suggest simpler examples. -/
class Shrinkable (α : Type u) [phSz : PhantomSizeOf α] where

  shrink : @ShrinkFn α phSz := λ _ => []
/-- `SampleableExt` generalizes the behavior of `Sampleable` and `Shrinkable`
and makes it possible to express instances for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.
For that purpose, `SampleableExt` provides a proxy representation
`proxy` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. -/
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

instance ofSampleable [Repr α] [Sampleable α] [PhantomSizeOf α] [Shrinkable α] : SampleableExt α where
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

/-- This can be specialized into customized `Sampleable Char` instances.
The resulting instance has `1 / length` chances of making an unrestricted choice of characters
and it otherwise chooses a character from `chars` with uniform probabilities.  -/
def Char.sampleable (length : Nat) (chars : List Char) (pos : 0 < chars.length) : Sampleable Char where
    sample := do
      let x ← choose Nat 0 length (Nat.zero_le _)
      if x.val == 0 then
        let n ← Sampleable.sample Nat
        pure $ Char.ofNat n
      else
        elements chars pos

instance Char.sampleableDefault : Sampleable Char :=
  Char.sampleable 3 " 0123abcABC:,;`\\/".toList (by decide)

instance Prod.sampleable [Repr α] [Repr β] [Sampleable α] [Sampleable β] : Sampleable (Prod α β) where
  sample := prodOf (Sampleable.sample α) (Sampleable.sample β)

end Samplers

section Shrinkers

/-- `Nat.shrink' n` creates a list of smaller natural numbers by
successively dividing `n` by 2 . For example, `Nat.shrink 5 = [2, 1, 0]`. -/
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
        simp only [sizeOfPhantom_eq_SizeOf]
        simp only [sizeOfPhantom_eq_SizeOf] at h2
        exact Nat.lt_trans h2 h
      })
  else
    []

instance Nat.shrinkable : Shrinkable Nat where
  shrink := Nat.shrink

/-- `Fin.shrink` works like `Nat.shrink` but instead operates on `Fin`. -/
def Fin.shrink {n : Nat} (m : Fin n.succ) : List { y : Fin n.succ // sizeOfPhantom.sizeOf y < sizeOfPhantom.sizeOf m } :=
  let shrinks := Nat.shrink m.val
  shrinks.map (λ x => {x with property := by
    have h := x.property
    simp [sizeOfPhantom_eq_SizeOf]
    simp [sizeOfPhantom_eq_SizeOf] at h
    exact Nat.succ_lt_succ $ lt_of_le_of_lt (Nat.mod_le _ _) h})

instance Fin.shrinkable {n : Nat} : Shrinkable (Fin n.succ) where
  shrink := Fin.shrink

local instance Int_sizeOfAbs : SizeOf Int := ⟨Int.natAbs⟩

/-- `Int.shrinkable` operates like `Nat.shrinkable` but also includes the negative variants. -/
instance Int.shrinkable : Shrinkable Int where
  shrink n :=
    Nat.shrink n.natAbs |>.map λ ⟨x, h⟩ => ⟨-x, (by rw [sizeOfPhantom_eq_SizeOf] at *; simp only [SizeOf.sizeOf]; rw [Int.natAbs_neg]; exact h)⟩

instance Bool.shrinkable : Shrinkable Bool := {}

/-- `Prod.shrink` returns one half of candidates with the first element
unchanged and the 2nd shrinked and the other half with the second element
unchanged and the 1st shrinked. -/
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

/-- An annotation for values that should never get shrinked. -/
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
