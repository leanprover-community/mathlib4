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
# Turing Reducibility and Turing Degrees

This file defines Turing reducibility and Turing equivalence in terms of oracle computability,
as well as the notion of Turing degrees as equivalence classes under mutual reducibility.

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

## Implementation notes

We define `TuringDegree` as the `Antisymmetrization` of the preorder of partial functions under
Turing reducibility. This gives a concrete representation of degrees as equivalence classes.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
* [Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers*, Vol. I.][Odifreddi1989] 

## Tags

Computability, Turing Degrees, Reducibility, Equivalence Relation
-/

@[expose] public section

open Std

/--
`f` is Turing reducible to `g` if `f` is partial recursive given access to the oracle `g`
-/
abbrev TuringReducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn {g} f

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel TuringReducible f g

@[inherit_doc] scoped[Computability] infix:50 " ≤ᵀ " => TuringReducible
@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent

open scoped Computability

variable {f g h : ℕ →. ℕ}

protected theorem TuringReducible.refl (f : ℕ →. ℕ) : f ≤ᵀ f := .oracle _ <| by simp
protected theorem TuringReducible.rfl : f ≤ᵀ f := .refl _

instance : Refl TuringReducible where refl _ := .rfl

theorem TuringReducible.trans (hg : f ≤ᵀ g) (hh : g ≤ᵀ h) : f ≤ᵀ h := by
  induction hg with
  | zero | succ | left | right => constructor
  | oracle g' hg' =>
    rw [Set.mem_singleton_iff] at hg'
    rw [hg']
    exact hh
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

instance : IsTrans (ℕ →. ℕ) TuringReducible :=
  ⟨@TuringReducible.trans⟩

instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := .refl

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
Instance declaring that `RecursiveIn` is a preorder.
-/
instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := TuringReducible.refl
  trans := @TuringReducible.trans

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

/--
`f` is Turing reducible to the join `f ⊕ g`.
-/
lemma left_le_join (f g : ℕ →. ℕ) : f ≤ᵀ (f ⊕ g) := by
  set j : ℕ →. ℕ := f ⊕ g
  have hj : RecursiveIn {j} j := RecursiveIn.oracle j (by simp)
  have hdouble : RecursiveIn {j} (fun n : ℕ => (2 * n : ℕ)) := by
    refine RecursiveIn.of_primrec (Primrec.nat_iff.1 ?_)
    simpa using (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
  have hdiv2 : RecursiveIn {j} (fun n : ℕ => (Nat.div2 n : ℕ)) := by
    refine RecursiveIn.of_primrec (Primrec.nat_iff.1 ?_)
    simpa using (Primrec.nat_div2 : Primrec Nat.div2)
  have hquery : RecursiveIn {j} (fun n => j (2 * n)) := by
    refine RecursiveIn.of_eq (RecursiveIn.comp hj hdouble) ?_
    intro n
    simp [Part.bind_some]
  have hdecode : RecursiveIn {j} (fun n => j (2 * n) >>= fun m => (Nat.div2 m : ℕ)) :=
    RecursiveIn.comp hdiv2 hquery
  have hf' : RecursiveIn {j} f := by
    refine RecursiveIn.of_eq hdecode ?_
    intro n
    have hcomp : (Nat.div2 ∘ fun y : ℕ => 2 * y) = (fun y => y) := by
      funext y
      simp [Function.comp, Nat.div2_bit0]
    simpa [j, join, Part.bind_some_eq_map, Part.map_map, Function.comp, hcomp] using
      (Part.map_id' (f := fun y : ℕ => y) (fun y => rfl) (f n))
  simpa [TuringReducible, j] using hf'

/--
`g` is Turing reducible to the join `f ⊕ g`.
-/
lemma right_le_join (f g : ℕ →. ℕ) : g ≤ᵀ (f ⊕ g) := by
  set j : ℕ →. ℕ := f ⊕ g
  have hj : RecursiveIn {j} j := RecursiveIn.oracle j (by simp)
  have hdouble1 : RecursiveIn {j} (fun n : ℕ => (2 * n + 1 : ℕ)) := by
    refine RecursiveIn.of_primrec (Primrec.nat_iff.1 ?_)
    simpa using
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1))
  have hdiv2 : RecursiveIn {j} (fun n : ℕ => (Nat.div2 n : ℕ)) := by
    refine RecursiveIn.of_primrec (Primrec.nat_iff.1 ?_)
    simpa using Primrec.nat_div2
  have hquery : RecursiveIn {j} (fun n => j (2 * n + 1)) := by
    refine RecursiveIn.of_eq (RecursiveIn.comp hj hdouble1) ?_
    intro n
    simp [Part.bind_some]
  have hdecode : RecursiveIn {j} (fun n => j (2 * n + 1) >>= fun m => (Nat.div2 m : ℕ)) :=
    RecursiveIn.comp hdiv2 hquery
  have hg' : RecursiveIn {j} g := by
    refine RecursiveIn.of_eq hdecode ?_
    intro n
    have hcomp : (Nat.div2 ∘ fun y : ℕ => 2 * y + 1) = (fun y => y) := by
      funext y
      simp [Function.comp]
    simpa [j, join, Part.bind_some_eq_map, Part.map_map, Function.comp, hcomp] using
      (Part.map_id' (f := fun y : ℕ => y) (fun y => rfl) (g n))
  simpa [TuringReducible, j] using hg'

/--
The join is recursive in the pair of oracles `{f, g}`.
-/
lemma join_recursiveIn_pair (f g : ℕ →. ℕ) : RecursiveIn ({f, g} : Set (ℕ →. ℕ)) (f ⊕ g) := by
  let O : Set (ℕ →. ℕ) := ({f, g} : Set (ℕ →. ℕ))
  have hpayload : RecursiveIn O (fun n : ℕ => (Nat.div2 n : ℕ)) := by
    refine RecursiveIn.of_primrec (O := O) ?_
    exact (Primrec.nat_iff.1 (by simpa using (Primrec.nat_div2 : Primrec Nat.div2)))
  have hdbl : RecursiveIn O (fun n : ℕ => (2 * n : ℕ)) := by
    refine RecursiveIn.of_primrec (O := O) ?_
    exact (Primrec.nat_iff.1 (by
      simpa using (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))
  have hdbl1 : RecursiveIn O (fun n : ℕ => (2 * n + 1 : ℕ)) := by
    refine RecursiveIn.of_primrec (O := O) ?_
    exact (Primrec.nat_iff.1 (by
      simpa using
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
          (Primrec.const 1))))
  have hfO : RecursiveIn O f := RecursiveIn.oracle f (by simp [O])
  have hgO : RecursiveIn O g := RecursiveIn.oracle g (by simp [O])
  let evenBranch : ℕ →. ℕ := fun n => (Nat.div2 n : ℕ) >>= f >>= fun y => (2 * y : ℕ)
  let oddBranch : ℕ →. ℕ := fun n => (Nat.div2 n : ℕ) >>= g >>= fun y => (2 * y + 1 : ℕ)
  have heven : RecursiveIn O evenBranch := by
    simpa [evenBranch] using RecursiveIn.comp hdbl (RecursiveIn.comp hfO hpayload)
  have hodd : RecursiveIn O oddBranch := by
    simpa [oddBranch] using RecursiveIn.comp hdbl1 (RecursiveIn.comp hgO hpayload)
  have hcond :
      RecursiveIn O (fun n => cond (Nat.bodd n) (oddBranch n) (evenBranch n)) :=
    RecursiveIn.cond (O := O) (c := Nat.bodd) (f := oddBranch) (g := evenBranch)
      (Computable.nat_bodd) hodd heven
  refine (RecursiveIn.of_eq (O := O) hcond ?_)
  intro n
  by_cases hbn : Nat.bodd n
  · simp [join, evenBranch, oddBranch, hbn, Part.bind_some_eq_map]
  · simp [join, evenBranch, oddBranch, hbn, Part.bind_some_eq_map]

/--
If `f` and `g` are both reducible to `h`, then their join is reducible to `h`.
-/
lemma join_le (f g h : ℕ →. ℕ) (hf : f ≤ᵀ h) (hg : g ≤ᵀ h) :
(f ⊕ g) ≤ᵀ h := by
  have hj : RecursiveIn ({f, g} : Set (ℕ →. ℕ)) (f ⊕ g) := join_recursiveIn_pair f g
  have hO : ∀ k, k ∈ ({f, g} : Set (ℕ →. ℕ)) → RecursiveIn ({h} : Set (ℕ →. ℕ)) k := by
    intro k hk
    have hk' : k = f ∨ k = g := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hk
    cases hk' with
    | inl hkf =>
        simpa [hkf] using hf
    | inr hkg =>
        simpa [hkg] using hg
  exact RecursiveIn.subst (O := ({f, g} : Set (ℕ →. ℕ))) (O' := ({h} : Set (ℕ →. ℕ)))
    (f := (f ⊕ g)) hj hO

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
