/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Vector.Defs

namespace Tactic.Polyrith.Groebner

structure Monomial (n : Nat) : Type where
  ofVec ::
    toVec : List.Vector Nat n
deriving DecidableEq

instance {n} : Mul (Monomial n) where
  mul a b := .ofVec (.map₂ (· + ·) a.toVec b.toVec)

def Monomial.gcd {n} (a b : Monomial n) : Monomial n :=
  .ofVec (.map₂ min a.toVec b.toVec)

def Monomial.lcm {n} (a b : Monomial n) : Monomial n :=
  .ofVec (.map₂ max a.toVec b.toVec)

structure Polynomial (𝕜 m : Type*) (cmp : m → m → Ordering) where
  protected ofArray ::
    protected toArray : Array (𝕜 × m)

def Polynomial.removeZero {𝕜 m cmp} [Zero 𝕜] [BEq 𝕜] (p : Polynomial 𝕜 m cmp) :
    Polynomial 𝕜 m cmp := .ofArray (p.toArray.filter (·.fst != 0))

instance {𝕜 m cmp} [Add 𝕜] [Zero 𝕜] [BEq 𝕜] : Add (Polynomial 𝕜 m cmp) where
  add a b := .removeZero <| .ofArray
    -- I wish `Array.mergeDedupWith` came with a version that would take `merge : α → α → Option α`
    (Array.mergeDedupWith (ord := {compare a b := cmp b.snd a.snd})
    a.toArray b.toArray (fun a b => (a.fst + b.fst, a.snd)))

instance {𝕜 m cmp} : Zero (Polynomial 𝕜 m cmp) where
  zero := .ofArray #[]

end Tactic.Polyrith.Groebner
