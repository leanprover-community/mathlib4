/-
Copyright (c) 2024 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Computability.Reduce
import Mathlib.Data.Part
import Mathlib.Order.Antisymmetrization
/-!
# Oracle Computability and Turing Degrees

This file defines a model of oracle computability, introduces Turing reducibility and equivalence,
proves that Turing equivalence is an equivalence relation, and defines Turing degrees as the
quotient under this relation.

## Main Definitions

- `RecursiveIn g f`:
  An inductive definition representing that a partial function `f` is recursive in oracle `g`.
- `TuringEquivalent`: A relation defining Turing equivalence between partial functions.
- `TuringDegree`:
  The type of Turing degrees, defined as equivalence classes under `TuringEquivalent`.

## Notation

- `f ≡ᵀ g` : `f` is Turing equivalent to `g`.

## Implementation Notes

The type of partial functions recursive in an oracle `g` is the smallest type containing
the constant zero, the successor, projections, the oracle `g`, and is closed under
pairing, composition, primitive recursion, and μ-recursion.

## References

* [Carneiro2018] Carneiro, Mario.
  *Formalizing Computability Theory via Partial Recursive Functions*.
  arXiv preprint arXiv:1810.08380, 2018.
* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers,
  Vol. I*. Springer-Verlag, 1989.
* [Soare1987] Soare, Robert I. *Recursively Enumerable Sets and Degrees*. Springer-Verlag, 1987.
* [Gu2015] Gu, Yi-Zhi. *Turing Degrees*. Institute for Advanced Study, 2015.

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

open Primrec Nat.Partrec Part

/--
The type of partial functions `f` that are recursive in an oracle `g` is the smallest type
containing the constant zero, the successor, left and right projections, the oracle `g`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.

Equivalently one can say that `f` is turing reducible to `g` when `f` is recursive in `g`.
-/

inductive RecursiveIn : (ℕ →. ℕ) → (ℕ →. ℕ) → Prop
  | zero (g) : RecursiveIn (fun _ => 0) g
  | succ (g) : RecursiveIn Nat.succ g
  | left (g) : RecursiveIn (fun n => (Nat.unpair n).1) g
  | right (g) : RecursiveIn (fun n => (Nat.unpair n).2) g
  | oracle (g) : RecursiveIn g g
  | pair (f h g : ℕ →. ℕ) (hf : RecursiveIn f g) (hh : RecursiveIn h g) :
      RecursiveIn (fun n => (Nat.pair <$> f n <*> h n)) g
  | comp (f h g : ℕ →. ℕ) (hf : RecursiveIn f g) (hh : RecursiveIn h g) :
      RecursiveIn (fun n => h n >>= f) g
  | prec (f h g : ℕ →. ℕ) (hf : RecursiveIn f g) (hh : RecursiveIn h g) :
      RecursiveIn (fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) (fun y ih => do
          let i ← ih
          h (Nat.pair a (Nat.pair y i)))) g
  | rfind (f g : ℕ →. ℕ) (hf : RecursiveIn f g) :
      RecursiveIn (fun a =>
        Nat.rfind (fun n => (fun m => m = 0) <$> f (Nat.pair a n))) g


/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel RecursiveIn f g

/--
Custom infix notation for `TuringEquivalent`.
-/
infix:50 " ≡ᵀ " => TuringEquivalent

/--
If a function is partial recursive, then it is recursive in every partial function.
-/

lemma Nat.Partrec.recursiveIn (f : ℕ →. ℕ) (pF : Nat.Partrec f) (g : ℕ →. ℕ) : RecursiveIn f g := by
  induction pF
  case zero =>
    apply RecursiveIn.zero
  case succ =>
    apply RecursiveIn.succ
  case left =>
    apply RecursiveIn.left
  case right =>
    apply RecursiveIn.right
  case pair f' g' _ _ ih1 ih2 =>
      apply RecursiveIn.pair f' g' g ih1 ih2
  case comp f' g' _ _ ih1 ih2 =>
    apply RecursiveIn.comp f' g' g ih1 ih2
  case prec f' g' _ _ ih1 ih2 =>
    apply RecursiveIn.prec f' g' g ih1 ih2
  case rfind f' _ ih =>
    apply RecursiveIn.rfind f' g ih

/--
If a function is recursive in the constant zero function,
then it is partial recursive.
-/
lemma RecursiveIn.partrec_of_zero (f : ℕ →. ℕ) (fRecInZero : RecursiveIn f fun _ => Part.some 0) :
  Nat.Partrec f := by
  generalize h : (fun _ => Part.some 0) = fp at *
  induction fRecInZero
  case zero =>
    apply Nat.Partrec.zero
  case succ =>
    apply Nat.Partrec.succ
  case left =>
    apply Nat.Partrec.left
  case right =>
    apply Nat.Partrec.right
  case oracle g =>
    rw [← h]
    apply Nat.Partrec.zero
  case pair _ _ _ _ ih1 ih2 =>
    apply Nat.Partrec.pair
    · apply ih1
      rw [← h]
    · apply ih2
      rw [← h]
  case comp _ _ _ _ ih1 ih2 =>
    apply Nat.Partrec.comp
    · apply ih1
      rw [← h]
    · apply ih2
      rw [← h]
  case prec _ _ _ _ ih1 ih2 =>
    apply Nat.Partrec.prec
    · apply ih1
      rw [← h]
    · apply ih2
      rw [← h]
  case rfind _ _ ih =>
    apply Nat.Partrec.rfind
    apply ih
    rw [← h]

/--
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
-/
theorem partrec_iff_partrec_in_everything (f : ℕ →. ℕ) : Nat.Partrec f ↔ ∀ g, RecursiveIn f g :=
  ⟨(·.recursiveIn), (· _ |>.partrec_of_zero)⟩

/--
Proof that turing reducibility is reflexive.
-/
theorem RecursiveIn.refl (f : ℕ →. ℕ) : RecursiveIn f f :=
  RecursiveIn.oracle f

/--
Instance declaring that `RecursiveIn` is reflexive.
-/
instance : IsRefl (ℕ →. ℕ) RecursiveIn :=
  ⟨fun f => RecursiveIn.refl f⟩

/--
Proof that turing reducibility is transitive.
-/
theorem RecursiveIn.trans {f g h : ℕ →. ℕ} (hg : RecursiveIn f g) (hh : RecursiveIn g h) :
  RecursiveIn f h := by
  induction hg
  case zero =>
    apply RecursiveIn.zero
  case succ =>
    apply RecursiveIn.succ
  case left =>
    apply RecursiveIn.left
  case right =>
    apply RecursiveIn.right
  case oracle =>
    exact hh
  case pair f' h' _ _ hf_ih hh_ih =>
    apply RecursiveIn.pair
    · apply hf_ih
      apply hh
    · apply hh_ih
      apply hh
  case comp f' h' _ _ hf_ih hh_ih =>
    apply RecursiveIn.comp
    · apply hf_ih
      apply hh
    · apply hh_ih
      apply hh
  case prec f' h' _ _ hf_ih hh_ih =>
    apply RecursiveIn.prec
    · apply hf_ih
      apply hh
    · apply hh_ih
      apply hh
  case rfind f' _ hf_ih =>
    apply RecursiveIn.rfind
    · apply hf_ih
      apply hh

/--
Instance declaring that `RecursiveIn` is transitive.
-/
instance : IsTrans (ℕ →. ℕ) RecursiveIn :=
  ⟨@RecursiveIn.trans⟩

/--
Instance declaring that `RecursiveIn` is a preorder.
-/
instance : IsPreorder (ℕ →. ℕ) RecursiveIn where
  refl := RecursiveIn.refl

/--
Instance declaring that `TuringEquivalent` is an equivalence relation.
-/
instance TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

/--
Proof that `TuringEquivalent` is reflexive.
-/
@[refl]
theorem TuringEquivalent.refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  Equivalence.refl equivalence f

/--
Proof that `TuringEquivalent` is symmetric.
-/
@[symm]
theorem TuringEquivalent.symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  Equivalence.symm equivalence h

/--
Proof that `TuringEquivalent` is transitive.
-/
@[trans]
theorem TuringEquivalent.trans (f g h : ℕ →. ℕ) (h1 : f ≡ᵀ g) (h2 : g ≡ᵀ h) : f ≡ᵀ h :=
  Equivalence.trans equivalence h1 h2

/--
The Turing degrees as the set of equivalence classes under Turing equivalence.
-/
abbrev TuringDegree :=
  Antisymmetrization _ RecursiveIn

/--
Instance declaring that `TuringDegree` is a partially ordered type.
-/
instance TuringDegree.isPartialOrder : PartialOrder TuringDegree :=
  @instPartialOrderAntisymmetrization (ℕ →. ℕ)
    {le := RecursiveIn, le_refl := .refl, le_trans _ _ _ := RecursiveIn.trans}
