/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Mathlib.Testing.SlimCheck.Gen
import Mathlib.Logic.Equiv.Functor
import Qq

#align_import testing.slim_check.sampleable from "leanprover-community/mathlib"@"fdc286cc6967a012f41b87f76dcd2797b53152af"

/-!
# `SampleableExt` Class

This class permits the creation samples of a given type
controlling the size of those values using the `Gen` monad.

# `Shrinkable` Class

This class helps minimize examples by creating smaller versions of
given values.

When testing a proposition like `∀ n : ℕ, prime n → n ≤ 100`,
`SlimCheck` requires that `ℕ` have an instance of `SampleableExt` and for
`prime n` to be decidable.  `SlimCheck` will then use the instance of
`SampleableExt` to generate small examples of ℕ and progressively increase
in size. For each example `n`, `prime n` is tested. If it is false,
the example will be rejected (not a test success nor a failure) and
`SlimCheck` will move on to other examples. If `prime n` is true,
`n ≤ 100` will be tested. If it is false, `n` is a counter-example of
`∀ n : ℕ, prime n → n ≤ 100` and the test fails. If `n ≤ 100` is true,
the test passes and `SlimCheck` moves on to trying more examples.

This is a port of the Haskell QuickCheck library.

## Main definitions

* `SampleableExt` class
* `Shrinkable` class

### `SampleableExt`

`SampleableExt` can be used in two ways. The first (and most common)
is to simply generate values of a type directly using the `Gen` monad,
if this is what you want to do then `SampleableExt.mkSelfContained` is
the way to go.

Furthermore it makes it possible to express generators for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.
For that purpose, `SampleableExt` provides a proxy representation
`proxy` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. If you
are using it in the first way, this proxy type will simply be the type
itself and the `interp` function `id`.

### `Shrinkable`

Given an example `x : α`, `Shrinkable α` gives us a way to shrink it
and suggest simpler examples.

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

set_option autoImplicit true

namespace SlimCheck

open Random Gen

/-- Given an example `x : α`, `Shrinkable α` gives us a way to shrink it
and suggest simpler examples. -/
class Shrinkable (α : Type u) where
  shrink : (x : α) → List α := λ _ => []

variable (m : Type v → Type u) [Monad m] -- [MonadLiftT (ST IO.RealWorld) m]

/-- `SampleableExt` can be used in two ways. The first (and most common)
is to simply generate values of a type directly using the `Gen` monad,
if this is what you want to do then `SampleableExt.mkSelfContained` is
the way to go.

Furthermore it makes it possible to express generators for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.
For that purpose, `SampleableExt` provides a proxy representation
`proxy` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. -/
class SampleableExt (α : Sort w) where
  proxy : Type v
  [proxyRepr : Repr proxy]
  [shrink : Shrinkable proxy]
  sample : Gen m proxy
  interp : proxy → α

attribute [instance] SampleableExt.proxyRepr
attribute [instance] SampleableExt.shrink

variable {m}

namespace SampleableExt

/-- Use to generate instance whose purpose is to simply generate values
of a type directly using the `Gen` monad -/
def mkSelfContained {α : Type v} [Repr α] [Shrinkable α] (sample : Gen m α) : SampleableExt m α where
  proxy := α
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := sample
  interp := id

/-- First samples a proxy value and interprets it. Especially useful if
the proxy and target type are the same. -/
def interpSample (α : Type v) [SampleableExt m α] : Gen m α :=
  SampleableExt.interp <$> SampleableExt.sample

end SampleableExt

section Shrinkers

/-- `Nat.shrink' n` creates a list of smaller natural numbers by
successively dividing `n` by 2 . For example, `Nat.shrink 5 = [2, 1, 0]`. -/
def Nat.shrink (n : Nat) : List Nat :=
  if h : 0 < n then
    let m := n/2
    have : m < n := by
      apply Nat.div_lt_self h
      decide
    m :: shrink m
  else
    []

instance Nat.shrinkable : Shrinkable Nat where
  shrink := Nat.shrink

instance Fin.shrinkable {n : Nat} : Shrinkable (Fin n.succ) where
  shrink m := Nat.shrink m

/-- `Int.shrinkable` operates like `Nat.shrinkable` but also includes the negative variants. -/
instance Int.shrinkable : Shrinkable Int where
  shrink n := Nat.shrink n.natAbs |>.map (λ x => ([x, -x] : List ℤ)) |>.join

instance Rat.shrinkable : Shrinkable Rat where
  shrink r :=
    (Shrinkable.shrink r.num).bind fun d => Nat.shrink r.den |>.map fun n => Rat.divInt d n

instance Bool.shrinkable : Shrinkable Bool := {}
instance Char.shrinkable : Shrinkable Char := {}

instance Prod.shrinkable [shrA : Shrinkable α] [shrB : Shrinkable β] :
    Shrinkable (Prod α β) where
  shrink := λ (fst,snd) =>
    let shrink1 := shrA.shrink fst |>.map fun x ↦ (x, snd)
    let shrink2 := shrB.shrink snd |>.map fun x ↦ (fst, x)
    shrink1 ++ shrink2

instance Sigma.shrinkable [shrA : Shrinkable α] [shrB : Shrinkable β] :
    Shrinkable ((_ : α) × β) where
  shrink := λ ⟨fst,snd⟩ =>
    let shrink1 := shrA.shrink fst |>.map fun x ↦ ⟨x, snd⟩
    let shrink2 := shrB.shrink snd |>.map fun x ↦ ⟨fst, x⟩
    shrink1 ++ shrink2
instance ULift.shrinkable [shr : Shrinkable α] : Shrinkable (ULift α) where
  shrink a := shr.shrink a.down |>.map fun x ↦ ⟨x⟩

open Shrinkable

/-- Shrink a list of a shrinkable type, either by discarding an element or shrinking an element. -/
instance List.shrinkable [Shrinkable α] : Shrinkable (List α) where
  shrink := fun L =>
    (L.mapIdx fun i _ => L.removeNth i) ++
    (L.mapIdx fun i a => (shrink a).map fun a' => L.modifyNth (fun _ => a') i).join

end Shrinkers

section Samplers

open SampleableExt

section univ_zero
variable {m : Type → Type v} [Monad m]

instance Nat.sampleableExt : SampleableExt m Nat :=
  mkSelfContained (do choose Nat 0 (← getSize) (Nat.zero_le _))

instance Fin.sampleableExt {n : Nat} :
    SampleableExt m (Fin (n.succ)) :=
  mkSelfContained (do choose (Fin n.succ) (Fin.ofNat 0) (Fin.ofNat (← getSize)) (by
    simp only [LE.le, Fin.ofNat, Nat.zero_mod, Fin.zero_eta, Fin.val_zero, Nat.le_eq]
    exact Nat.zero_le _))

instance Int.sampleableExt : SampleableExt m Int :=
  mkSelfContained (do
    choose Int (-(← getSize)) (← getSize)
      (le_trans (Int.neg_nonpos_of_nonneg (Int.ofNat_zero_le _)) (Int.ofNat_zero_le _)))

instance Rat.sampleableExt : SampleableExt m Rat :=
  mkSelfContained (do
    let d ← choose Int (-(← getSize)) (← getSize)
      (le_trans (Int.neg_nonpos_of_nonneg (Int.ofNat_zero_le _)) (Int.ofNat_zero_le _))
    let n ← choose Nat 0 (← getSize) (Nat.zero_le _)
    return Rat.divInt d n)

instance Bool.sampleableExt : SampleableExt m Bool :=
  mkSelfContained $ chooseAny Bool

/-- This can be specialized into customized `SampleableExt Char` instances.
The resulting instance has `1 / length` chances of making an unrestricted choice of characters
and it otherwise chooses a character from `chars` with uniform probabilities.  -/
def Char.sampleable [LawfulMonad m] (length : Nat) (chars : List Char) (pos : 0 < chars.length) :
    SampleableExt m Char :=
  mkSelfContained do
    let x ← choose Nat 0 length (Nat.zero_le _)
    if x.val == 0 then
      let n ← interpSample Nat
      pure $ Char.ofNat n
    else
      elements chars pos

instance Char.sampleableDefault [LawfulMonad m] : SampleableExt m Char :=
  Char.sampleable 3 " 0123abcABC:,;`\\/".toList (by decide)

instance Prop.sampleableExt : SampleableExt m Prop where
  proxy := Bool
  proxyRepr := inferInstance
  sample := interpSample Bool
  shrink := inferInstance
  interp := Coe.coe
end univ_zero

instance : ULiftable Id.{u} Id.{v} := inferInstance

attribute [pp_with_univ] SampleableExt

instance Prod.sampleableExt.{up₁,up₂} {α : Type u₁} {β : Type u₂}
    {m₁ : Type up₁ → Type v₁} {m₂ : Type up₂ → Type v₂} {m : Type (max up₁ up₂) → Type v₃}
    [ULiftable m₁ m] [ULiftable m₂ m] [Monad m₁] [Monad m₂] [Monad m]
    [SampleableExt m₁ α] [SampleableExt m₂ β] :
    SampleableExt m (α × β) where
  proxy := Prod (proxy _ α) (proxy _ β)
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := prodOf (sample (m := m₁)) (sample (m := m₂))
  interp := Prod.map interp interp

instance List.sampleableExt {m₀} [Monad m₀] [ULiftable m₀ m] [SampleableExt m α] :
    SampleableExt m (List α) where
  proxy := List (proxy _ α)
  sample := Gen.listOf sample
  interp := List.map interp

instance ULift.sampleableExt {α : Type u₁}
    {m₁ : Type u₁ → Type v} {m : Type (max u₁ u₂) → Type v}
    [ULiftable m₁ m] [Monad m₁] [Monad m] [SampleableExt m₁ α] :
    SampleableExt m (ULift.{u₂} α) where
  proxy := ULift.{u₂} (proxy m₁ α)
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := ULiftable.up sample
  interp := ULift.map interp

end Samplers

/-- An annotation for values that should never get shrinked. -/
def NoShrink (α : Type u) := α

namespace NoShrink

def mk (x : α) : NoShrink α := x
def get (x : NoShrink α) : α := x

instance inhabited [inst : Inhabited α] : Inhabited (NoShrink α) := inst
instance repr [inst : Repr α] : Repr (NoShrink α) := inst

instance shrinkable : Shrinkable (NoShrink α) where
  shrink := λ _ => []

instance sampleableExt [SampleableExt m α] [Repr α] : SampleableExt m (NoShrink α) :=
  SampleableExt.mkSelfContained $ (NoShrink.mk ∘ SampleableExt.interp) <$> SampleableExt.sample

end NoShrink

/--
Print (at most) 10 samples of a given type to stdout for debugging.

The generator must live in a monad `m` such that:
* There is an analogous monad `m₀` in universe 0
* `m₀` can be lifted to `IO`
-/
def printSamples {t : Type v} [Repr t] {m₀}
    [MonadLiftT m₀ IO] [MonadLiftT (ST IO.RealWorld) m₀] [ULiftable m₀ m] (g : Gen m t) :
    IO PUnit := do
  let f : m₀ (List Lean.Format) := ULiftable.down (do
    let xs ← (List.range 10).mapM g.run
    pure <| ULift.up (xs.map repr))
  -- let xsr ← runRand <| ULiftable.down <| (do
  --   let xs ← (List.range 10).mapM fun i => ULift.up (g.run ⟨i⟩)
  --   pure <| Ulift.up (xs.map repr))
  --     -- let f : Rand m (ULift.{v} Lean.Format) := do return ⟨repr (← g ⟨i⟩)⟩
  --     -- let f : Rand m' Lean.Format := ULiftable.down f
      -- let ⟨s⟩ ← ULiftable.up (do repr (← g.run i))
  let xsr ← f
  for x in xsr do
    IO.println x
open Lean Meta Qq

/-- Create a `Gen IO α` expression from the argument of `#sample` -/
def mkGenerator (e : Expr) : MetaM (Expr × Expr) := do
  let t ← inferType e
  match t.getAppFnArgs with
  | (`Gen, #[t]) => do
    let repr_inst ← synthInstance (← mkAppM ``Repr #[t])
    pure (repr_inst, e)
  | _ => do
    let sampleableExt_inst ← synthInstance
      (← mkAppM ``SampleableExt #[← mkConstWithFreshMVarLevels ``IO, e])
    let repr_inst ← mkAppOptM ``SampleableExt.proxyRepr #[none, e, sampleableExt_inst]
    let gen ← mkAppOptM ``SampleableExt.sample #[none, none, sampleableExt_inst]
    pure (repr_inst, gen)

open Elab

/--
`#sample type`, where `type` has an instance of `SampleableExt`, prints ten random
values of type `type` using an increasing size parameter.

```lean
#sample Nat
-- prints
-- 0
-- 0
-- 2
-- 24
-- 64
-- 76
-- 5
-- 132
-- 8
-- 449
-- or some other sequence of numbers

#sample List Int
-- prints
-- []
-- [1, 1]
-- [-7, 9, -6]
-- [36]
-- [-500, 105, 260]
-- [-290]
-- [17, 156]
-- [-2364, -7599, 661, -2411, -3576, 5517, -3823, -968]
-- [-643]
-- [11892, 16329, -15095, -15461]
-- or whatever
```
-/
elab "#sample " e:term : command =>
  Command.runTermElabM fun _ => do
    let e ← Elab.Term.elabTermAndSynthesize e none
    let (repr_inst, gen) ← mkGenerator e
    let printSamples ← mkAppOptM ``printSamples
      #[none, none, none, repr_inst, q(IO), none, none, none, gen]
    let code ← unsafe evalExpr (IO PUnit) q(IO PUnit) printSamples
    _ ← code

end SlimCheck
