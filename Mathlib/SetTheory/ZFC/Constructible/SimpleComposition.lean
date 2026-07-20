/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.SimpleSubstitution

/-!
# Composition of simple set functions

This file proves that strong simplicity is preserved by unary and binary composition. The tuple
renamings below arrange arguments and intermediate values for the corresponding bounded formulas.
-/

@[expose] public section

universe u

namespace Constructible.Godel

/-- Move the distinguished value immediately following the argument block to
the front, leaving the trailing context in place. -/
def rotateAfterArgs (n k : Nat) : Fin (n + (1 + k)) → Fin (1 + (n + k)) :=
  fun i => Fin.addCases
    (fun j : Fin n => Fin.natAdd 1 (Fin.castAdd k j))
    (fun j : Fin (1 + k) => Fin.addCases
      (fun _ : Fin 1 => (0 : Fin (1 + (n + k))))
      (fun l : Fin k =>
        Fin.natAdd 1 (Fin.natAdd n l)) j) i

theorem addCases_comp_rotateAfterArgs {A : Type u} (n k : Nat)
    (args : Tuple A n) (value : A) (extra : Tuple A k) :
    (fun i =>
      Fin.addCases (fun _ : Fin 1 => value) (Fin.addCases args extra)
        (rotateAfterArgs n k i)) =
      Fin.addCases args (Fin.addCases (fun _ : Fin 1 => value) extra) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [rotateAfterArgs]
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro l
      fin_cases l
      simp only [rotateAfterArgs, Fin.addCases_right, Fin.addCases_left]
      change Fin.addCases
          (fun _ : Fin 1 => value)
          (fun i : Fin (n + k) => Fin.addCases args extra i)
          (Fin.castAdd (n + k) (0 : Fin 1)) = value
      simpa only [] using
        (Fin.addCases_left
          (motive := fun _ => A)
          (left := fun _ : Fin 1 => value)
          (right := fun i : Fin (n + k) =>
            Fin.addCases (motive := fun _ => A) args extra i)
          (0 : Fin 1))
    · intro l
      simp only [rotateAfterArgs, Fin.addCases_right]

/-- Identify two consecutive copies of the same argument tuple. -/
def diagonalRename (n k : Nat) : Fin (n + (n + k)) → Fin (n + k) :=
  Fin.addCases (fun i => Fin.castAdd k i) (fun i => i)

theorem addCases_comp_diagonalRename {A : Type u} (n k : Nat)
    (args : Tuple A n) (extra : Tuple A k) :
    (fun i : Fin (n + (n + k)) =>
      Fin.addCases (motive := fun _ => A) args extra
        (diagonalRename n k i)) =
      (fun i : Fin (n + (n + k)) =>
        Fin.addCases (motive := fun _ => A) args
          (fun j : Fin (n + k) =>
            Fin.addCases (motive := fun _ => A) args extra j) i) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · simp only [diagonalRename, Fin.addCases_left]
  · simp only [diagonalRename, Fin.addCases_right]

/-- The two-component tuple formed by two set-valued functions. -/
def binaryTuple {n : Nat}
    (f g : Tuple ZFSet.{u} n → ZFSet.{u})
    (args : Tuple ZFSet.{u} n) : Tuple ZFSet.{u} 2 :=
  fun i => Fin.cases (f args) (fun _ => g args) i

/-- Reassociate a two-coordinate output followed by a context. -/
def unflattenPairContext (k : Nat) : Fin (2 + k) → Fin (1 + (1 + k)) :=
  fun i => Fin.addCases
    (fun j : Fin 2 => Fin.cases 0
      (fun _ : Fin 1 => Fin.natAdd 1 (0 : Fin (1 + k))) j)
    (fun l : Fin k => Fin.natAdd 1 (Fin.natAdd 1 l)) i

theorem nested_comp_unflattenPairContext {n k : Nat}
    (f g : Tuple ZFSet.{u} n → ZFSet.{u})
    (args : Tuple ZFSet.{u} n) (extra : Tuple ZFSet.{u} k) :
    (fun i : Fin (2 + k) =>
      Fin.addCases (fun _ : Fin 1 => f args)
        (fun j : Fin (1 + k) =>
          Fin.addCases (fun _ : Fin 1 => g args) extra j)
        (unflattenPairContext k i)) =
      Fin.addCases (binaryTuple f g args) extra := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Fin.addCases_left]
      change Fin.addCases
          (fun _ : Fin 1 => f args)
          (fun j : Fin (1 + k) =>
            Fin.addCases (fun _ : Fin 1 => g args) extra j)
          (Fin.castAdd (1 + k) (0 : Fin 1)) = f args
      exact Fin.addCases_left (0 : Fin 1)
    · simp only [Fin.mk_one, Fin.isValue, Fin.addCases_left]
      change Fin.addCases
          (fun _ : Fin 1 => f args)
          (fun j : Fin (1 + k) =>
            Fin.addCases (fun _ : Fin 1 => g args) extra j)
          (Fin.natAdd 1 (0 : Fin (1 + k))) = g args
      exact (Fin.addCases_right (0 : Fin (1 + k))).trans
        (Fin.addCases_left (0 : Fin 1))
  · intro j
    simp only [unflattenPairContext, Fin.addCases_right]

/-- Two simple functions can be substituted simultaneously as a two-tuple. -/
theorem IsSimpleSetFunction.binaryTuple {n : Nat}
    {f g : Tuple ZFSet.{u} n → ZFSet.{u}}
    (hf : IsSimpleSetFunction f) (hg : IsSimpleSetFunction g) :
    IsSimpleTupleMap (binaryTuple f g) := by
  intro k phi
  let nestedPhi : Delta0Formula (1 + (1 + k)) :=
    Delta0Formula.rename (unflattenPairContext k) phi
  rcases hf (1 + k) nestedPhi with ⟨afterF, hafterF⟩
  let rotated : Delta0Formula (1 + (n + k)) :=
    Delta0Formula.rename (rotateAfterArgs n k) afterF
  rcases hg (n + k) rotated with ⟨afterG, hafterG⟩
  refine ⟨Delta0Formula.rename (diagonalRename n k) afterG, ?_⟩
  intro args extra
  rw [Delta0Formula.satisfies_rename,
    addCases_comp_diagonalRename]
  rw [hafterG args (Fin.addCases args extra)]
  simp only [rotated, Delta0Formula.satisfies_rename,
    addCases_comp_rotateAfterArgs]
  rw [hafterF args
    (Fin.addCases (fun _ : Fin 1 => g args) extra)]
  simp only [nestedPhi, Delta0Formula.satisfies_rename]
  rw [nested_comp_unflattenPairContext]

/-- Binary composition of simple set functions. -/
theorem IsSimpleSetFunction.compBinary {n : Nat}
    {outer : Tuple ZFSet.{u} 2 → ZFSet.{u}}
    {left right : Tuple ZFSet.{u} n → ZFSet.{u}}
    (hOuter : IsSimpleSetFunction outer)
    (hLeft : IsSimpleSetFunction left)
    (hRight : IsSimpleSetFunction right) :
    IsSimpleSetFunction
      (fun args => outer
        (_root_.Constructible.Godel.binaryTuple left right args)) :=
  hOuter.compTuple (IsSimpleSetFunction.binaryTuple hLeft hRight)

end Constructible.Godel
