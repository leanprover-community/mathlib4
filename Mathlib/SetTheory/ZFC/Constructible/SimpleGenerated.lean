/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.SimpleCompiler

/-!
# Generated bounded formulas for simple set functions

This file derives reusable elimination formulas from `SimpleValueSpec` and proves the resulting
strong-simplicity theorem for ternary membership descriptions.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n : Nat}

/-- Place the uniform graph formula for an operation at arbitrary
coordinates. -/
def opEqAt (i : Fin 9) {n : Nat} (out x y : Fin n) :
    Delta0Formula n :=
  Delta0Formula.rename ![out, x, y] (opGraphFormula i)

@[simp]
theorem satisfies_opEqAt (i : Fin 9) {n : Nat}
    (out x y : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (opEqAt i out x y) s ↔
      s out = op i (s x) (s y) := by
  rw [opEqAt, Delta0Formula.satisfies_rename]
  have hassign : (fun j => s (![out, x, y] j)) =
      ![s out, s x, s y] := by
    funext j
    fin_cases j <;> rfl
  rw [hassign]
  exact satisfies_opGraphFormula i (s out) (s x) (s y)

/-- A strong-simple function can replace the final coordinate of any bounded
formula, while its arguments are placed before the untouched context. -/
theorem exists_eliminateSimpleLast {r n : Nat}
    {f : Tuple ZFSet.{u} r → ZFSet.{u}}
    (hf : IsSimpleSetFunction f) (φ : Delta0Formula (n + 1)) :
    ∃ ψ : Delta0Formula (r + n),
      ∀ (args : Tuple ZFSet.{u} r) (s : Tuple ZFSet.{u} n),
        Satisfies ZFMem ψ (Fin.addCases args s) ↔
          Satisfies ZFMem φ (snoc s (f args)) := by
  rcases hf n (Delta0Formula.rename (lastToFirst n) φ) with
    ⟨ψ, hψ⟩
  refine ⟨ψ, ?_⟩
  intro args s
  rw [hψ args s, Delta0Formula.satisfies_rename]
  have hassign :
      (fun i => Fin.addCases (fun _ : Fin 1 => f args) s
        (lastToFirst n i)) = snoc s (f args) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [snoc_last]
      have hlast : lastToFirst n (Fin.last n) =
          (0 : Fin (1 + n)) := by simp [lastToFirst]
      rw [hlast]
      rfl
    · simp [lastToFirst]
  rw [hassign]

noncomputable def eliminateSimpleLast {r n : Nat}
    {f : Tuple ZFSet.{u} r → ZFSet.{u}}
    (hf : IsSimpleSetFunction f) (φ : Delta0Formula (n + 1)) :
    Delta0Formula (r + n) :=
  Classical.choose (exists_eliminateSimpleLast hf φ)

@[simp]
theorem satisfies_eliminateSimpleLast {r n : Nat}
    {f : Tuple ZFSet.{u} r → ZFSet.{u}}
    (hf : IsSimpleSetFunction f) (φ : Delta0Formula (n + 1))
    (args : Tuple ZFSet.{u} r) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eliminateSimpleLast hf φ) (Fin.addCases args s) ↔
      Satisfies ZFMem φ (snoc s (f args)) :=
  Classical.choose_spec (exists_eliminateSimpleLast hf φ) args s

/-- The right-associated triple operation is strong-simple. -/
theorem isSimpleSetFunction_triple :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 3 => triple (s 0) (s 1) (s 2)) := by
  have hright : IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 3 => ZFSet.pair (s 1) (s 2)) := by
    have h := isSimpleSetFunction_orderedPair.compBinary
      (isSimpleSetFunction_projection.{u} (1 : Fin 3))
      (isSimpleSetFunction_projection.{u} (2 : Fin 3))
    have hOne : (1 : Fin 2) = Fin.succ 0 := by rfl
    simpa only [binaryTuple, hOne, Fin.cases_zero, Fin.cases_succ] using h
  have h := isSimpleSetFunction_orderedPair.compBinary
    (isSimpleSetFunction_projection.{u} (0 : Fin 3)) hright
  have hOne : (1 : Fin 2) = Fin.succ 0 := by rfl
  simpa only [binaryTuple, triple, hOne, Fin.cases_zero,
    Fin.cases_succ] using h

/-- Put three leading coordinates after an untouched context. -/
def tripleFirstToLast (n : Nat) : Fin (3 + n) → Fin (n + 3) :=
  Fin.addCases
    (fun i : Fin 3 => Fin.cases
      (Fin.last n).castSucc.castSucc
      (fun j : Fin 2 => Fin.cases
        (Fin.last (n + 1)).castSucc
        (fun _ : Fin 1 => Fin.last (n + 2)) j) i)
    (fun i : Fin n => i.castSucc.castSucc.castSucc)

theorem tripleFirstToLast_assignment (s : Tuple ZFSet.{u} n)
    (x y z : ZFSet.{u}) :
    (fun i => snoc (snoc (snoc s x) y) z (tripleFirstToLast n i)) =
      Fin.addCases ![x, y, z] s := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    · simp [tripleFirstToLast]
    · change snoc (snoc (snoc s x) y) z
        (Fin.last (n + 1)).castSucc = y
      simp
    · change snoc (snoc (snoc s x) y) z (Fin.last (n + 2)) = z
      simp
  · intro j
    simp [tripleFirstToLast]

end Constructible.Godel
