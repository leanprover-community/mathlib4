/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Vector.Defs
import Mathlib.Algebra.Notation.Defs

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

instance {𝕜 m cmp} [Neg 𝕜] : Neg (Polynomial 𝕜 m cmp) where
  neg a := .ofArray (a.toArray.map fun c => (-c.fst, c.snd))

instance {𝕜 m cmp} : Zero (Polynomial 𝕜 m cmp) where
  zero := .ofArray #[]

instance {𝕜 m cmp} [Mul 𝕜] : SMul 𝕜 (Polynomial 𝕜 m cmp) where
  smul a b := .ofArray (b.toArray.map fun p => (a * p.fst, p.snd))

instance {𝕜 m cmp} [Mul m] : SMul m (Polynomial 𝕜 m cmp) where
  smul a b := .ofArray (b.toArray.map fun p => (p.fst, a * p.snd))

def Polynomial.lead {𝕜 m cmp} (p : Polynomial 𝕜 m cmp) (h : p ≠ 0) : 𝕜 × m :=
  p.toArray[0]'(Array.size_pos_iff.mpr fun ha => h (congrArg Polynomial.ofArray ha))

def Polynomial.leadCoeff {𝕜 m cmp} (p : Polynomial 𝕜 m cmp) (h : p ≠ 0) : 𝕜 :=
  (p.toArray[0]'(Array.size_pos_iff.mpr fun ha => h (congrArg Polynomial.ofArray ha))).fst

def Polynomial.leadMon {𝕜 m cmp} (p : Polynomial 𝕜 m cmp) (h : p ≠ 0) : m :=
  (p.toArray[0]'(Array.size_pos_iff.mpr fun ha => h (congrArg Polynomial.ofArray ha))).snd

end Tactic.Polyrith.Groebner
