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
- `turing_reducible`: A relation defining Turing reducibility between partial functions.
- `turing_equivalent`: A relation defining Turing equivalence between partial functions.
- `TuringDegree`:
  The type of Turing degrees, defined as equivalence classes under `turing_equivalent`.
- `join`: Combines two partial functions into one by =
  mapping even and odd numbers to respective functions.

## Notation

- `f ≤ᵀ g` : `f` is Turing reducible to `g`.
- `f ≡ᵀ g` : `f` is Turing equivalent to `g`.
- `f ⊕ g` : The join of partial functions `f` and `g`.

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

open Primrec Nat.Partrec Part

/--
The type of partial functions `f` that are recursive in an oracle `g` is the smallest type
containing the constant zero, the successor, left and right projections, the oracle `g`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.
-/
inductive RecursiveIn : (ℕ →. ℕ) → (ℕ →. ℕ) → Prop
  | zero {g} : RecursiveIn (fun _ => 0) g
  | succ {g} : RecursiveIn Nat.succ g
  | left {g} : RecursiveIn (fun n => (Nat.unpair n).1) g
  | right {g} : RecursiveIn (fun n => (Nat.unpair n).2) g
  | oracle {g} : RecursiveIn g g
  | pair {f h g : ℕ →. ℕ} (hf : RecursiveIn f g) (hh : RecursiveIn h g) :
      RecursiveIn (fun n => (Nat.pair <$> f n <*> h n)) g
  | comp {f h g : ℕ →. ℕ} (hf : RecursiveIn f g) (hh : RecursiveIn h g) :
      RecursiveIn (fun n => h n >>= f) g
  | prec {f h g : ℕ →. ℕ} (hf : RecursiveIn f g) (hh : RecursiveIn h g) :
      RecursiveIn (fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) (fun y ih => do
          let i ← ih
          h (Nat.pair a (Nat.pair y i)))) g
  | rfind {f g : ℕ →. ℕ} (hf : RecursiveIn f g) :
      RecursiveIn (fun a =>
        Nat.rfind (fun n => (fun m => m = 0) <$> f (Nat.pair a n))) g


/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
def turing_equivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel RecursiveIn f g

/--
Custom infix notation for `turing_equivalent`.
-/
infix:50 " ≡ᵀ " => turing_equivalent

/--
If a function is partial recursive, then it is recursive in every partial function.
-/
lemma partrec_implies_recursive_in_everything
  (f : ℕ →. ℕ) : Nat.Partrec f → (∀ g, RecursiveIn f g) := by
    intro pF
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
      apply RecursiveIn.rfind ih

/--
If a function is recursive in the constant zero function,
then it is partial recursive.
-/
lemma partrec_in_zero_implies_partrec
(f : ℕ →. ℕ) : RecursiveIn f (fun _ => Part.some 0) → Nat.Partrec f := by
  intro fRecInZero
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
A partial function `f` is partial recursive if and only if it is
recursive in the constant zero function.
-/
lemma partrec_iff_partrec_in_zero
  (f : ℕ →. ℕ) : Nat.Partrec f ↔ RecursiveIn f (fun _ => Part.some 0) := by
  constructor
  · intro pF
    apply partrec_implies_recursive_in_everything
    assumption
  · intro h
    apply partrec_in_zero_implies_partrec
    assumption

/--
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
-/
theorem partrec_iff_partrec_in_everything
  (f : ℕ →. ℕ) : Nat.Partrec f ↔ (∀ g, RecursiveIn f g) := by
  constructor
  · exact partrec_implies_recursive_in_everything f
  · intro H
    have lem : RecursiveIn f (fun _ => Part.some 0) := H (fun _ => Part.some 0)
    rw [← partrec_iff_partrec_in_zero] at lem
    exact lem

/--
Proof that `turing_reducible` is reflexive.
-/
theorem turing_reducible_refl (f : ℕ →. ℕ) : RecursiveIn f f :=
  RecursiveIn.oracle

/--
Proof that `turing_equivalent` is reflexive.
-/
@[refl]
theorem turing_equivalent_refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  ⟨turing_reducible_refl f, turing_reducible_refl f⟩

/--
Proof that `turing_equivalent` is symmetric.
-/
@[symm]
theorem turing_equivalent_symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  ⟨h.2, h.1⟩

/--
Proof that `turing_reducible` is transitive.
-/
@[trans]
theorem turing_reducible_trans {f g h : ℕ →. ℕ} :
  RecursiveIn f g → RecursiveIn g h → RecursiveIn f h := by
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
Instance declaring that `RecursiveIn` is a preorder.
-/
instance : IsPreorder (ℕ →. ℕ) RecursiveIn where
  refl := turing_reducible_refl
  trans := @turing_reducible_trans

/--
The Turing degrees as the set of equivalence classes under Turing equivalence.
-/
def TuringDegree :=
  Antisymmetrization _ RecursiveIn

/--
The `join` function combines two partial functions `f` and `g` into a single partial function.
For a given input `n`:

- **If `n` is even**:
  - It checks if `f` is defined at `n / 2`.
  - If so, `join f g` is defined at `n` with the value `2 * f(n / 2)`.

- **If `n` is odd**:
  - It checks if `g` is defined at `n / 2`.
  - If so, `join f g` is defined at `n` with the value `2 * g(n / 2) + 1`.
-/
def join (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  fun n =>
    if n % 2 = 0 then
      (f (n / 2)).map (fun x => 2 * x)
    else
      (g (n / 2)).map (fun y => 2 * y + 1)

/-- Join notation `f ⊕ g` is the "join" of partial functions `f` and `g`. -/
infix:99 "⊕" => join

/--
For any partial functions `a`, `b₁`, and `b₂`, if `b₁` is Turing equivalent to `b₂`,
then `a` is Turing reducible to `b₁` if and only if `a` is Turing reducible to `b₂`.
-/
lemma reduce_lifts₁ : ∀ (a b₁ b₂ : ℕ →. ℕ), b₁≡ᵀb₂ → (RecursiveIn a b₁) = (RecursiveIn a b₂) := by
  intros a b₁ b₂ bEqb
  apply propext
  constructor
  · intro aRedb₁
    apply turing_reducible_trans aRedb₁ bEqb.1
  · intro aRedb₂
    apply turing_reducible_trans aRedb₂ bEqb.2

/--
For any partial functions `f`, `g`, and `h`, if `f` is Turing equivalent to `g`,
then `f` is Turing reducible to `h` if and only if `g` is Turing reducible to `h`.
-/
lemma reduce_lifts₂ : ∀ (f g h : ℕ →. ℕ),
f ≡ᵀ g → (RecursiveIn f h = RecursiveIn g h) := by
  intros f g h fEqg
  apply propext
  constructor
  · intro fRedh
    apply turing_reducible_trans fEqg.2 fRedh
  · intro gRedh
    apply turing_reducible_trans fEqg.1 gRedh

/--
Here we show how to lift the Turing reducibility relation from
partial functions to their Turing degrees, using the above lemmas.
-/
def TuringDegree.turing_red (d₁ d₂ : TuringDegree) : Prop :=
  @Quot.lift₂ _ _ Prop (turing_equivalent)
  (turing_equivalent) (RecursiveIn) (reduce_lifts₁) (reduce_lifts₂) d₁ d₂

/--
Instance declaring that `TuringDegree.turing_red` is a partial order.
-/
instance : PartialOrder TuringDegree where
  le := TuringDegree.turing_red
  le_refl := by
    apply Quot.ind
    intro a
    apply turing_reducible_refl
  le_trans := by
    apply Quot.ind
    intro a
    apply Quot.ind
    intro b
    apply Quot.ind
    intro c
    exact turing_reducible_trans
  le_antisymm := by
    apply Quot.ind
    intro a
    apply Quot.ind
    intro b
    intros aRedb bReda
    apply Quot.sound
    constructor
    · exact aRedb
    · exact bReda
