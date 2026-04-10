/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/

module

public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.NormNum
public import Mathlib.Computability.RecursiveIn
import Aesop

/-!
# Turing degrees

This file defines Turing reducibility and equivalence, proves that Turing equivalence is an
equivalence relation, and defines Turing degrees as the quotient under this relation.

## Main definitions

* `TuringReducible f g`:
  The function `f` is Turing reducible to `g` if `f` is recursive in the singleton set `{g}`.
* `TuringEquivalent f g`:
  Functions `f` and `g` are Turing equivalent if they are mutually Turing reducible.
* `TuringDegree`:
  The type of Turing degrees, given by the quotient of `ℕ →. ℕ` under `TuringEquivalent`.

## Notation

* `f ≤ᵀ g`: `f` is Turing reducible to `g`.
* `f ≡ᵀ g`: `f` is Turing equivalent to `g`.

## References

* [Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers*, Vol. I.]
  [Odifreddi1989]

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

@[expose] public section

open Primrec Std

variable {f g h : ℕ →. ℕ}

/--
`f` is Turing reducible to `g` if `f` is partial recursive given access to the oracle `g`
-/
abbrev TuringReducible (f g : ℕ →. ℕ) : Prop :=
  Nat.RecursiveIn {g} f

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel TuringReducible f g

@[inherit_doc] scoped[Computability] infix:50 " ≤ᵀ " => TuringReducible
@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent

open scoped Computability

/-- If a function is partial recursive, then it is recursive in every partial function. -/
lemma Partrec.turingReducible (pF : Partrec f) : f ≤ᵀ g :=
  RecursiveIn.iff_nat.1 pF.recursiveIn

/-- If a function is recursive in a constant partial function, then it is partial recursive. -/
lemma TuringReducible.partrec_of_const {s} (hf : f ≤ᵀ fun _ => s) : Partrec f :=
  RecursiveIn.partrec_of_const (RecursiveIn.iff_nat.2 hf)

/-- A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`. -/
theorem partrec_iff_forall_turingReducible : Partrec f ↔ ∀ g, f ≤ᵀ g :=
  ⟨fun hf _ => hf.turingReducible, fun hf => hf (fun _ => .none) |>.partrec_of_const⟩

protected theorem TuringReducible.refl (f : ℕ →. ℕ) : f ≤ᵀ f := .oracle _ <| by simp
protected theorem TuringReducible.rfl : f ≤ᵀ f := .refl _

theorem TuringReducible.trans (hg : f ≤ᵀ g) (hh : g ≤ᵀ h) : f ≤ᵀ h :=
  hg.subst (by simpa using hh)

instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := TuringReducible.refl
  trans := @TuringReducible.trans

theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

@[refl]
protected theorem TuringEquivalent.refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  Equivalence.refl equivalence f

@[symm]
theorem TuringEquivalent.symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  Equivalence.symm equivalence h

@[trans]
theorem TuringEquivalent.trans (f g h : ℕ →. ℕ) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h) : f ≡ᵀ h :=
  Equivalence.trans equivalence h₁ h₂

/--
Turing degrees are the equivalence classes of partial functions under Turing equivalence.
-/
abbrev TuringDegree :=
  Antisymmetrization _ TuringReducible

set_option backward.privateInPublic true in
private instance : Preorder (ℕ →. ℕ) where
  le := TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans

instance TuringDegree.instPartialOrder : PartialOrder TuringDegree :=
  instPartialOrderAntisymmetrization

open scoped Computability Partrec
open Encodable Partrec

/-- `f` is Turing reducible to the join `f ⊕ g`. -/
lemma left_le_join (f g : ℕ →. ℕ) : f ≤ᵀ (f ⊕ g) := by
  set j := f ⊕ g
  have hj := Nat.RecursiveIn.oracle j
    (show j ∈ ({j} : Set _) by simp)
  refine (Nat.RecursiveIn.div2.comp
    (hj.comp_at_even)).of_eq fun n => ?_
  simp only [Join.even, Part.bind_eq_bind, Part.bind_map, j]
  simp [Nat.div2_bit0]

/-- `g` is Turing reducible to the join `f ⊕ g`. -/
lemma right_le_join (f g : ℕ →. ℕ) : g ≤ᵀ (f ⊕ g) := by
  set j := f ⊕ g
  have hj := Nat.RecursiveIn.oracle j
    (show j ∈ ({j} : Set _) by simp)
  refine (Nat.RecursiveIn.div2.comp
    (hj.comp_at_odd)).of_eq fun n => ?_
  simp only [Join.odd, Part.bind_eq_bind, Part.bind_map, j]
  simp

/-- The join is recursive in the pair of oracles `{f, g}`. -/
lemma join_recursiveIn_pair (f g : ℕ →. ℕ) :
    Nat.RecursiveIn ({f, g} : Set (ℕ →. ℕ)) (f ⊕ g) := by
  set O : Set (ℕ →. ℕ) := {f, g}
  have hfO : Nat.RecursiveIn O f := .oracle f (by simp [O])
  have hgO : Nat.RecursiveIn O g := .oracle g (by simp [O])
  refine (Nat.RecursiveIn.cond' Computable.nat_bodd
    (hgO.encode_odd) (hfO.encode_even)).of_eq fun n => ?_
  by_cases hbn : Nat.bodd n <;>
    simp [join, hbn, Part.bind_some_eq_map]

/-- If `f` and `g` are both reducible to `h`, then their join
is reducible to `h`. -/
lemma join_le (f g h : ℕ →. ℕ) (hf : f ≤ᵀ h) (hg : g ≤ᵀ h) :
    (f ⊕ g) ≤ᵀ h :=
  (join_recursiveIn_pair f g).subst fun k hk => by
    rcases Set.mem_insert_iff.mp hk with rfl | hkg
    · exact hf
    · rw [Set.mem_singleton_iff.mp hkg]; exact hg

namespace TuringDegree

/-- The Turing join respects Turing reducibility: if `f ≤ᵀ f'` and `g ≤ᵀ g'`,
then `f ⊕ g ≤ᵀ f' ⊕ g'`. -/
theorem join_mono {f f' g g' : ℕ →. ℕ} (hf : f ≤ᵀ f') (hg : g ≤ᵀ g') :
    (f ⊕ g) ≤ᵀ (f' ⊕ g') := by
  have hf' : f ≤ᵀ (f' ⊕ g') := hf.trans (left_le_join f' g')
  have hg' : g ≤ᵀ (f' ⊕ g') := hg.trans (right_le_join f' g')
  exact join_le f g (f' ⊕ g') hf' hg'

/-- The Turing join respects Turing equivalence. -/
theorem join_congr {f f' g g' : ℕ →. ℕ} (hf : f ≡ᵀ f') (hg : g ≡ᵀ g') :
    (f ⊕ g) ≡ᵀ (f' ⊕ g') :=
  ⟨join_mono hf.1 hg.1, join_mono hf.2 hg.2⟩

/-- The supremum operation on Turing degrees, induced by the Turing join. -/
def sup : TuringDegree → TuringDegree → TuringDegree :=
  Quotient.lift₂
    (fun f g => toAntisymmetrization TuringReducible (f ⊕ g))
    (fun _ _ _ _ hf hg => Quotient.sound (join_congr hf hg))

/-- `sup` agrees with `⊕` on representatives. -/
lemma sup_mk (f g : ℕ →. ℕ) :
    TuringDegree.sup (toAntisymmetrization TuringReducible f)
    (toAntisymmetrization TuringReducible g) =
    toAntisymmetrization TuringReducible (f ⊕ g) := rfl

instance instSemilatticeSup : SemilatticeSup TuringDegree where
  sup := sup
  le_sup_left a b := by
    induction a using Quotient.inductionOn'
    induction b using Quotient.inductionOn'
    exact left_le_join _ _
  le_sup_right a b := by
    induction a using Quotient.inductionOn'
    induction b using Quotient.inductionOn'
    exact right_le_join _ _
  sup_le {a b c} ha hb := by
    induction a using Quotient.inductionOn'
    induction b using Quotient.inductionOn'
    induction c using Quotient.inductionOn'
    exact join_le _ _ _ ha hb

/-- The sup on Turing degrees agrees with the Turing join on representatives. -/
@[simp]
lemma sup_def (f g : ℕ →. ℕ) :
    (toAntisymmetrization TuringReducible f) ⊔ (toAntisymmetrization TuringReducible g) =
    toAntisymmetrization TuringReducible (f ⊕ g) := rfl

end TuringDegree
