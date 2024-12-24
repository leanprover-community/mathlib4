/-
Copyright (c) 2024 Tanner Duve, Elan Roth
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Computability.Reduce
import Mathlib.Data.Part

/-!
# Oracle Computability and Turing Degrees

This file defines a model of oracle computability, introduces Turing reducibility and equivalence,
proves that Turing equivalence is an equivalence relation, and defines Turing degrees as the
quotient under this relation.

## Main Definitions

- `RecursiveIn g f`:
  An inductive definition representing that a partial function `f` is recursive in oracle `g`.
- `turing_reducible`: A relation defining Turing reducibility between partial functions.
- `turing_equivalent`: A relation defining Turing equivalence between partial functions.
- `TuringDegree`:
  The type of Turing degrees, defined as equivalence classes under `turing_equivalent`.

## Notation

- `f ≤ᵀ g` : `f` is Turing reducible to `g`.
- `f ≡ᵀ g` : `f` is Turing equivalent to `g`.
- `f ⊔ g` : The join of partial functions `f` and `g`.

## Implementation Notes

The type of partial functions recursive in an oracle `g` is the smallest type containing
the constant zero, the successor, projections, the oracle `g`, and is closed under
pairing, composition, primitive recursion, and μ-recursion. The `join` operation
combines two partial functions into a single partial function by mapping even and odd
numbers to the respective functions.

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

open Primrec Nat.Partrec

/--
The type of partial functions recursive in an oracle `g` is the smallest type containing
the constant zero, the successor, left and right projections, the oracle `g`, and is closed under
pairing, composition, primitive recursion, and μ-recursion.
-/
inductive RecursiveIn (g : ℕ →. ℕ) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn g (fun _ => 0)
  | succ : RecursiveIn g Nat.succ
  | left : RecursiveIn g (fun n => (Nat.unpair n).1)
  | right : RecursiveIn g (fun n => (Nat.unpair n).2)
  | oracle : RecursiveIn g g
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn g f) (hh : RecursiveIn g h) :
      RecursiveIn g (fun n => (Nat.pair <$> f n <*> h n))
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn g f) (hh : RecursiveIn g h) :
      RecursiveIn g (fun n => h n >>= f)
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn g f) (hh : RecursiveIn g h) :
      RecursiveIn g (fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) (fun y ih => do
          let i ← ih
          h (Nat.pair a (Nat.pair y i))))
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn g f) :
      RecursiveIn g (fun a =>
        Nat.rfind (fun n => (fun m => m = 0) <$> f (Nat.pair a n)))

/--
`f` is Turing reducible to `g` if `f` is recursive in `g`.
-/
def turing_reducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn g f
/--
Custom infix notation for `turing_reducible`.
-/
infix:50 " ≤ᵀ " => turing_reducible

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
def turing_equivalent (f g : ℕ →. ℕ) : Prop :=
  f ≤ᵀ g ∧ g ≤ᵀ f
/--
Custom infix notation for `turing_equivalent`.
-/
infix:50 " ≡ᵀ " => turing_equivalent

/--
A partial function `f` is partial recursive if and only if
it is recursive in the constant zero function.
-/
lemma partrec_iff_partrec_in_zero
  (f : ℕ →. ℕ) : Nat.Partrec f ↔ RecursiveIn (fun _ => pure 0) f := by
  constructor
  { intro pF
    induction' pF
    case mp.zero =>
      apply RecursiveIn.zero
    case mp.succ =>
      apply RecursiveIn.succ
    case mp.left =>
      apply RecursiveIn.left
    case mp.right =>
      apply RecursiveIn.right
    case mp.pair _ _ _ _ ih1 ih2 =>
      apply RecursiveIn.pair ih1 ih2
    case mp.comp _ _ _ _ ih1 ih2 =>
      apply RecursiveIn.comp ih1 ih2
    case mp.prec _ _ _ _ ih1 ih2 =>
      apply RecursiveIn.prec ih1 ih2
    case mp.rfind _ _ ih =>
      apply RecursiveIn.rfind ih }
  { intro fRecInNone
    induction' fRecInNone
    case mpr.zero =>
      apply Nat.Partrec.zero
    case mpr.succ =>
      apply Nat.Partrec.succ
    case mpr.left =>
      apply Nat.Partrec.left
    case mpr.right =>
      apply Nat.Partrec.right
    case mpr.oracle =>
      apply Nat.Partrec.zero
    case mpr.pair _ _ _ _ ih1 ih2 =>
      apply Nat.Partrec.pair ih1 ih2
    case mpr.comp _ _ _ _ ih1 ih2 =>
      apply Nat.Partrec.comp ih1 ih2
    case mpr.prec _ _ _ _ ih1 ih2 =>
      apply Nat.Partrec.prec ih1 ih2
    case mpr.rfind _ _ ih =>
      apply Nat.Partrec.rfind ih }

 /--
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
-/
theorem partrec_iff_partrec_in_everything
  (f : ℕ →. ℕ) : Nat.Partrec f ↔ (∀ g, RecursiveIn g f) := by
  constructor
  { intro pF
    intro g
    induction pF
    case zero =>
      apply RecursiveIn.zero
    case succ =>
      apply RecursiveIn.succ
    case left =>
      apply RecursiveIn.left
    case right =>
      apply RecursiveIn.right
    case pair _ _ _ _ ih1 ih2 =>
      apply RecursiveIn.pair ih1 ih2
    case comp _ _ _ _ ih1 ih2 =>
      apply RecursiveIn.comp ih1 ih2
    case prec _ _ _ _ ih1 ih2 =>
      apply RecursiveIn.prec ih1 ih2
    case rfind _ _ ih =>
      apply RecursiveIn.rfind ih }
  { intro H
    have lem : RecursiveIn (fun _ => pure 0) f := H (fun _ => pure 0)
    rw [← partrec_iff_partrec_in_zero] at lem
    exact lem }

 /--
Proof that `turing_reducible` is reflexive.
-/
theorem turing_reducible_refl (f : ℕ →. ℕ) : f ≤ᵀ f :=
  RecursiveIn.oracle

 /--
Proof that `turing_equivalent` is reflexive.
-/
theorem turing_equivalent_refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  ⟨turing_reducible_refl f, turing_reducible_refl f⟩

 /--
Proof that `turing_equivalent` is symmetric.
-/
theorem turing_equivalent_symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  ⟨h.2, h.1⟩

 /--
Proof that `turing_reducible` is transitive.
-/
theorem turing_reducible_trans {f g h : ℕ →. ℕ} :
  f ≤ᵀ g → g ≤ᵀ h → f ≤ᵀ h := by
  intro hg hh
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
    { apply hf_ih }
    { apply hh_ih }
  case comp f' h' _ _ hf_ih hh_ih =>
    apply RecursiveIn.comp
    { apply hf_ih }
    { apply hh_ih }
  case prec f' h' _ _ hf_ih hh_ih =>
    apply RecursiveIn.prec
    { apply hf_ih }
    { apply hh_ih }
  case rfind f' _ hf_ih =>
    apply RecursiveIn.rfind
    { apply hf_ih }

 /--
Proof that `turing_equivalent` is transitive.
-/
theorem turing_equivalent_trans :
  Transitive turing_equivalent :=
  fun _ _ _ ⟨fg₁, fg₂⟩ ⟨gh₁, gh₂⟩ =>
    ⟨turing_reducible_trans fg₁ gh₁, turing_reducible_trans gh₂ fg₂⟩

 /--
Instance declaring that `turing_equivalent` is an equivalence relation.
-/
instance : Equivalence turing_equivalent :=
  {
    refl := turing_equivalent_refl,
    symm := turing_equivalent_symm,
    trans := @turing_equivalent_trans
  }

/--
The Turing degrees as the set of equivalence classes under Turing equivalence.
-/
def TuringDegree :=
  Quot turing_equivalent

/--
The `join` function combines two partial functions `f` and `g` into a single partial function.
It maps even numbers to the result of `f` applied to half the number,
and odd numbers to the result of `g` applied to half the number.
-/
def join (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  fun n =>
    if n % 2 = 0 then
      (f (n / 2)).map (fun x => 2 * x)
    else
      (g (n / 2)).map (fun y => 2 * y + 1)

/-- Join notation `f ⊔ g` is the "join" of partial functions `f` and `g`. -/
infix:99 "⊔" => join

#lint
