/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.SimplePairSets
public import Mathlib.SetTheory.ZFC.Constructible.SimpleTerms

/-!
# Compiling simple set functions

This file packages the data needed to eliminate a binary set-valued operation from bounded
formulas and proves the generic correctness lemmas for that elimination procedure.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n m k : Nat}

/-- Data sufficient to eliminate one binary set-valued operation from every
bounded context.  `boundAt` is the only operation-specific higher-order
clause; membership and graph formulas handle all atomic occurrences. -/
structure SimpleValueSpec where
  eval : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
  memAt : {n : Nat} → Fin n → Fin n → Fin n → Delta0Formula n
  eqAt : {n : Nat} → Fin n → Fin n → Fin n → Delta0Formula n
  boundAt : {n : Nat} → Fin n → Fin n →
    Delta0Formula (n + 1) → Delta0Formula n
  satisfies_memAt : ∀ {n : Nat} (q x y : Fin n)
    (s : Tuple ZFSet.{u} n),
    Satisfies ZFMem (memAt q x y) s ↔ s q ∈ eval (s x) (s y)
  satisfies_eqAt : ∀ {n : Nat} (out x y : Fin n)
    (s : Tuple ZFSet.{u} n),
    Satisfies ZFMem (eqAt out x y) s ↔ s out = eval (s x) (s y)
  satisfies_boundAt : ∀ {n : Nat} (x y : Fin n)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n),
    Satisfies ZFMem (boundAt x y body) s ↔
      ∃ z ∈ eval (s x) (s y), Satisfies ZFMem body (snoc s z)

/-- An expression is either a target variable or the one distinguished value
described by a `SimpleValueSpec`. -/
inductive ValueExpr (n : Nat)
  | var (i : Fin n)
  | value (left right : Fin n)

namespace ValueExpr

def eval (spec : SimpleValueSpec.{u}) (s : Tuple ZFSet.{u} n) :
    ValueExpr n → ZFSet.{u}
  | .var i => s i
  | .value i j => spec.eval (s i) (s j)

def rename (ρ : Fin n → Fin m) : ValueExpr n → ValueExpr m
  | .var i => .var (ρ i)
  | .value i j => .value (ρ i) (ρ j)

@[simp]
theorem eval_rename (spec : SimpleValueSpec.{u})
    (ρ : Fin n → Fin m) (s : Tuple ZFSet.{u} m) (e : ValueExpr n) :
    (e.rename ρ).eval spec s = e.eval spec (fun i => s (ρ i)) := by
  cases e <;> rfl

/-- Any two structured expressions in a valid substitution are the same
distinguished value. -/
def Compatible : ValueExpr n → ValueExpr n → Prop
  | .value x y, .value x' y' => x = x' ∧ y = y'
  | _, _ => True

theorem compatible_rename (ρ : Fin n → Fin m)
    {left right : ValueExpr n} (h : left.Compatible right) :
    (left.rename ρ).Compatible (right.rename ρ) := by
  cases left <;> cases right
  · trivial
  · trivial
  · trivial
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

end ValueExpr

def ValueSubstCompatible {m n : Nat} (σ : Fin m → ValueExpr n) : Prop :=
  ∀ i j, (σ i).Compatible (σ j)

def memValueExpr (spec : SimpleValueSpec.{u}) {n : Nat} :
    ValueExpr n → ValueExpr n → Delta0Formula n
  | .var a, .var b => .mem a b
  | .var a, .value x y => spec.memAt a x y
  | .value x y, .var a =>
      .boundedEx a (spec.eqAt (Fin.last n) x.castSucc y.castSucc)
  | .value x _, .value _ _ => .neg (.eq x x)

def eqValueExpr (spec : SimpleValueSpec.{u}) {n : Nat} :
    ValueExpr n → ValueExpr n → Delta0Formula n
  | .var a, .var b => .eq a b
  | .var a, .value x y => spec.eqAt a x y
  | .value x y, .var a => spec.eqAt a x y
  | .value x _, .value _ _ => .eq x x

@[simp]
theorem satisfies_memValueExpr (spec : SimpleValueSpec.{u}) {n : Nat}
    (left right : ValueExpr n) (h : left.Compatible right)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memValueExpr spec left right) s ↔
      left.eval spec s ∈ right.eval spec s := by
  cases left with
  | var a =>
      cases right with
      | var b => rfl
      | value x y => exact spec.satisfies_memAt a x y s
  | value x y =>
      cases right with
      | var a =>
          simp only [memValueExpr, Satisfies, spec.satisfies_eqAt,
            ValueExpr.eval, snoc_last, snoc_castSucc]
          constructor
          · rintro ⟨z, hz, heq⟩
            simpa [heq] using hz
          · intro hmem
            exact ⟨spec.eval (s x) (s y), hmem, rfl⟩
      | value x' y' =>
          rcases h with ⟨rfl, rfl⟩
          simp [memValueExpr, ValueExpr.eval, ZFSet.mem_irrefl]

@[simp]
theorem satisfies_eqValueExpr (spec : SimpleValueSpec.{u}) {n : Nat}
    (left right : ValueExpr n) (h : left.Compatible right)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqValueExpr spec left right) s ↔
      left.eval spec s = right.eval spec s := by
  cases left <;> cases right
  · rfl
  · exact spec.satisfies_eqAt _ _ _ s
  · exact (spec.satisfies_eqAt _ _ _ s).trans eq_comm
  · rcases h with ⟨rfl, rfl⟩
    simp [eqValueExpr, ValueExpr.eval]

def liftValueSubst {m n : Nat} (σ : Fin m → ValueExpr n) :
    Fin (m + 1) → ValueExpr (n + 1) :=
  Fin.lastCases (.var (Fin.last n))
    (fun i => (σ i).rename Fin.castSucc)

theorem eval_liftValueSubst (spec : SimpleValueSpec.{u}) {m n : Nat}
    (σ : Fin m → ValueExpr n) (s : Tuple ZFSet.{u} n)
    (z : ZFSet.{u}) :
    (fun i => (liftValueSubst σ i).eval spec (snoc s z)) =
      snoc (fun i => (σ i).eval spec s) z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [liftValueSubst, ValueExpr.eval]
  · cases h : σ j <;>
      simp [liftValueSubst, ValueExpr.eval, ValueExpr.rename, h]

theorem valueSubstCompatible_lift {m n : Nat}
    {σ : Fin m → ValueExpr n} (hσ : ValueSubstCompatible σ) :
    ValueSubstCompatible (liftValueSubst σ) := by
  intro i j
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [liftValueSubst, ValueExpr.Compatible]
  · refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [liftValueSubst, ValueExpr.Compatible]
    · simpa [liftValueSubst] using
        (ValueExpr.compatible_rename Fin.castSucc (hσ i' j'))

/-- Uniform arbitrary-context compiler from a `SimpleValueSpec`. -/
def compileValueSubst (spec : SimpleValueSpec.{u}) {m n : Nat}
    (σ : Fin m → ValueExpr n) : Delta0Formula m → Delta0Formula n
  | .mem i j => memValueExpr spec (σ i) (σ j)
  | .eq i j => eqValueExpr spec (σ i) (σ j)
  | .neg φ => .neg (compileValueSubst spec σ φ)
  | .conj φ ψ =>
      .conj (compileValueSubst spec σ φ) (compileValueSubst spec σ ψ)
  | .boundedEx i φ =>
      match σ i with
      | .var bound =>
          .boundedEx bound
            (compileValueSubst spec (liftValueSubst σ) φ)
      | .value left right =>
          spec.boundAt left right
            (compileValueSubst spec (liftValueSubst σ) φ)

@[simp]
theorem satisfies_compileValueSubst (spec : SimpleValueSpec.{u})
    {m n : Nat} (σ : Fin m → ValueExpr n)
    (hσ : ValueSubstCompatible σ) (φ : Delta0Formula m)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (compileValueSubst spec σ φ) s ↔
      Satisfies ZFMem φ (fun i => (σ i).eval spec s) := by
  induction φ generalizing n with
  | mem i j =>
      exact satisfies_memValueExpr spec (σ i) (σ j) (hσ i j) s
  | eq i j =>
      exact satisfies_eqValueExpr spec (σ i) (σ j) (hσ i j) s
  | neg φ ih => simp [compileValueSubst, ih σ hσ]
  | conj φ ψ ihφ ihψ =>
      simp [compileValueSubst, ihφ σ hσ, ihψ σ hσ]
  | boundedEx i φ ih =>
      cases hbound : σ i with
      | var bound =>
          simp only [compileValueSubst, hbound, Satisfies]
          constructor
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [ValueExpr.eval, hbound] using hz
            · rw [ih (liftValueSubst σ)
                (valueSubstCompatible_lift hσ)] at hφ
              simpa only [eval_liftValueSubst] using hφ
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [ValueExpr.eval, hbound] using hz
            · rw [ih (liftValueSubst σ)
                (valueSubstCompatible_lift hσ)]
              simpa only [eval_liftValueSubst] using hφ
      | value left right =>
          rw [compileValueSubst, hbound, spec.satisfies_boundAt]
          constructor
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [ValueExpr.eval, hbound] using hz
            · rw [ih (liftValueSubst σ)
                (valueSubstCompatible_lift hσ)] at hφ
              simpa only [eval_liftValueSubst] using hφ
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [ValueExpr.eval, hbound] using hz
            · rw [ih (liftValueSubst σ)
                (valueSubstCompatible_lift hσ)]
              simpa only [eval_liftValueSubst] using hφ

def valueContextSubst (k : Nat) : Fin (1 + k) → ValueExpr (2 + k) :=
  Fin.addCases
    (fun _ => .value
      (Fin.castAdd k (0 : Fin 2)) (Fin.castAdd k (1 : Fin 2)))
    (fun i => .var (Fin.natAdd 2 i))

theorem valueContextSubst_compatible (k : Nat) :
    ValueSubstCompatible (valueContextSubst k) := by
  intro i j
  refine Fin.addCases ?_ ?_ i
  · intro a
    fin_cases a
    refine Fin.addCases ?_ ?_ j
    · intro b
      fin_cases b
      exact ⟨rfl, rfl⟩
    · intro b
      simp [valueContextSubst, ValueExpr.Compatible]
  · intro a
    refine Fin.addCases ?_ ?_ j
    · intro b
      simp [valueContextSubst, ValueExpr.Compatible]
    · intro b
      simp [valueContextSubst, ValueExpr.Compatible]

theorem eval_valueContextSubst (spec : SimpleValueSpec.{u})
    (x y : ZFSet.{u}) (extra : Tuple ZFSet.{u} k) :
    (fun i => (valueContextSubst k i).eval spec
      (Fin.addCases ![x, y] extra)) =
      Fin.addCases (fun _ : Fin 1 => spec.eval x y) extra := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    rfl
  · intro j
    simp [valueContextSubst, ValueExpr.eval]

theorem SimpleValueSpec.isSimple (spec : SimpleValueSpec.{u}) :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => spec.eval (s 0) (s 1)) := by
  intro k φ
  refine ⟨compileValueSubst spec (valueContextSubst k) φ, ?_⟩
  intro args extra
  rw [satisfies_compileValueSubst spec _
    (valueContextSubst_compatible k)]
  have hargs : args = ![args 0, args 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hargs, eval_valueContextSubst]
  simp

end Constructible.Godel
