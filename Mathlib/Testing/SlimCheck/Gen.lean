import Mathlib.Control.Random
import Mathlib.Data.List.Perm
import Mathlib.Data.Subtype
import Mathlib.Data.Nat.Basic

namespace SlimCheck

open Random

abbrev Gen (α : Type u) := ReaderT (ULift Nat) Rand α

/-- Lift `Random.random` to the `Gen` monad. -/
def chooseAny (α : Type u) [Random α] : Gen α :=
  λ _ => rand α

/-- Lift `BoundedRandom.randomR` to the `Gen` monad. -/
def choose (α : Type u) [Preorder α] [BoundedRandom α] (lo hi : α) (h : lo ≤ hi) : Gen {a // lo ≤ a ∧ a ≤ hi} :=
  λ _ => randBound α lo hi h

lemma chooseNatLt_aux {lo hi : Nat} (a : Nat) (h : Nat.succ lo ≤ a ∧ a ≤ hi) : lo ≤ Nat.pred a ∧ Nat.pred a < hi :=
  And.intro
    (Nat.le_pred_of_lt (Nat.lt_of_succ_le h.left))
    (have : a.pred.succ ≤ hi := by
       rw [Nat.succ_pred_eq_of_pos]
       exact h.right
       exact lt_of_le_of_lt (Nat.zero_le lo) h.left
     this
    )

def chooseNatLt (lo hi : Nat) (h : lo < hi) : Gen {a // lo ≤ a ∧ a < hi} :=
  Subtype.map Nat.pred chooseNatLt_aux <$> choose Nat (lo.succ) hi (Nat.succ_le_of_lt h)

def getSize : Gen Nat :=
  read >>= pure ∘ ULift.down

def sized (f : Nat → Gen α) : Gen α :=
  getSize >>= f

def resize (f : Nat → Nat) (x : Gen α) : Gen α :=
  withReader (ULift.up ∘ f ∘ ULift.down) x

def arrayOf (x : Gen α) : Gen (Array α) := do
  let sz ← choose Nat 0 (←getSize) (Nat.zero_le _)
  let mut res := #[]
  for i in [0:sz] do
    res := res.push (←x)
  pure res

def listOf (x : Gen α) : Gen (List α) :=
  arrayOf x >>= pure ∘ Array.toList

def oneOf (xs : List (Gen α)) (pos : 0 < xs.length) : Gen α := do
  let ⟨x, h1, h2⟩ ← chooseNatLt 0 xs.length pos
  xs.get ⟨x, h2⟩

def elements (xs : List α) (pos : 0 < xs.length) : Gen α := do
  let ⟨x, h1, h2⟩ ← chooseNatLt 0 xs.length pos
  pure $ xs.get ⟨x, h2⟩

open List in
def permutationOf : (xs : List α) → Gen { ys // ys ~ xs }
| [] => pure ⟨[], Perm.nil⟩
| x::xs => do
  let ⟨ys, h1⟩ ← permutationOf xs
  let ⟨n, h2, h3⟩ ← choose Nat 0 ys.length (Nat.zero_le _)
  pure ⟨insertNth n x ys, Perm.trans (perm_insertNth h3) (Perm.cons _ h1)⟩

/-- Execute a `Gen` inside the `IO` monad using `size` as the example size-/
def IO.runGen (x : Gen α) (size : Nat) : BaseIO α :=
  IO.runRand $ ReaderT.run x ⟨size⟩

end SlimCheck
