/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.SimpleGenerated

/-!
# Simplicity of the Gödel operations F6 and F8

This file instantiates the generic simple-function compiler for component extraction, fibers, and
the remaining bounded pair-component operation represented here by F6 and F8.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n : Nat}

/-- The pair coordinate in the component-witness layout. -/
def componentPairIndex (n : Nat) : Fin (n + 5) :=
  (Fin.last n).castSucc.castSucc.castSucc.castSucc

/-- The left-component coordinate in the component-witness layout. -/
def componentLeftIndex (n : Nat) : Fin (n + 5) :=
  (Fin.last (n + 2)).castSucc.castSucc

/-- The right-component coordinate in the component-witness layout. -/
def componentRightIndex (n : Nat) : Fin (n + 5) :=
  Fin.last (n + 4)

/-- Select one component and the final witness coordinate. -/
def componentLastRename (useRight : Bool) (n : Nat) :
    Fin (n + 1) → Fin (n + 5) :=
  Fin.lastCases
    (if useRight then componentRightIndex n else componentLeftIndex n)
    (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem componentLastRename_assignment (useRight : Bool)
    (s : Tuple ZFSet.{u} n) (p leftBox left rightBox right : ZFSet.{u}) :
    let extended := snoc (snoc (snoc (snoc (snoc s p) leftBox) left)
      rightBox) right
    (fun i => extended (componentLastRename useRight n i)) =
      snoc s (if useRight then right else left) := by
  dsimp only
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [snoc_last]
    cases useRight
    · simp [componentLastRename, componentLeftIndex]
    · simp [componentLastRename, componentRightIndex]
  · simp [componentLastRename]

/-- A candidate member of F6 is the right component of a pair in `x`. -/
def f6GeneratedBody {n : Nat} (body : Delta0Formula (n + 1)) :
    Delta0Formula (n + 5) :=
  .conj
    (kuratowskiPairEqAt (componentPairIndex n)
      (componentLeftIndex n) (componentRightIndex n))
    (Delta0Formula.rename (componentLastRename true n) body)

theorem satisfies_f6GeneratedBody (body : Delta0Formula (n + 1))
    (s : Tuple ZFSet.{u} n)
    (p leftBox left rightBox right : ZFSet.{u}) :
    Satisfies ZFMem (f6GeneratedBody body)
        (snoc (snoc (snoc (snoc (snoc s p) leftBox) left)
          rightBox) right) ↔
      p = ZFSet.pair left right ∧
        Satisfies ZFMem body (snoc s right) := by
  simp only [f6GeneratedBody, Satisfies, satisfies_kuratowskiPairEqAt,
    componentPairIndex, componentLeftIndex, componentRightIndex,
    snoc_last, snoc_castSucc, Delta0Formula.satisfies_rename]
  rw [componentLastRename_assignment]
  rfl

/-- Eliminate a bounded quantifier over an F6 value. -/
def f6BoundAt {n : Nat} (x _y : Fin n)
    (body : Delta0Formula (n + 1)) : Delta0Formula n :=
  withBoundedPairComponents x (f6GeneratedBody body)

@[simp]
theorem satisfies_f6BoundAt {n : Nat} (x y : Fin n)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (f6BoundAt x y body) s ↔
      ∃ q ∈ F6 (s x) (s y), Satisfies ZFMem body (snoc s q) := by
  simp only [f6BoundAt, satisfies_withBoundedPairComponents,
    satisfies_f6GeneratedBody]
  constructor
  · rintro ⟨p, hp, leftBox, hleftBox, left, hleft,
      rightBox, hrightBox, right, hright, hpEq, hbody⟩
    refine ⟨right, ?_, hbody⟩
    exact mem_F6_iff.mpr ⟨left, by simpa [hpEq] using hp⟩
  · rintro ⟨right, hrightF6, hbody⟩
    rcases mem_F6_iff.mp hrightF6 with ⟨left, hp⟩
    refine ⟨ZFSet.pair left right, hp, ({left} : ZFSet.{u}), ?_,
      left, ?_, ({left, right} : ZFSet.{u}), ?_, right, ?_, rfl, hbody⟩
    · simp [ZFSet.pair]
    · simp
    · simp [ZFSet.pair]
    · simp

/-- The simple-value specification for F6. -/
noncomputable def f6Spec : SimpleValueSpec.{u} where
  eval := F6
  memAt := memOpAt 6
  eqAt := opEqAt 6
  boundAt := f6BoundAt
  satisfies_memAt := by
    intro n q x y s
    exact satisfies_memOpAt (6 : Fin 9) q x y s
  satisfies_eqAt := by
    intro n out x y s
    exact satisfies_opEqAt (6 : Fin 9) out x y s
  satisfies_boundAt := by
    intro n x y body s
    exact satisfies_f6BoundAt x y body s

theorem isSimpleSetFunction_F6 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F6 (s 0) (s 1)) := by
  simpa only [f6Spec] using f6Spec.{u}.isSimple

/-! ## Fibers are simple -/

/-- A bounded formula for membership in a fiber. -/
def fiberMemAt {n : Nat} (q x z : Fin n) : Delta0Formula n :=
  .boundedEx x
    (kuratowskiPairEqAt (Fin.last n) q.castSucc z.castSucc)

@[simp]
theorem satisfies_fiberMemAt {n : Nat} (q x z : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (fiberMemAt q x z) s ↔
      s q ∈ fiber (s x) (s z) := by
  simp only [fiberMemAt, Satisfies, satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc, mem_fiber_iff]
  constructor
  · rintro ⟨p, hp, hpEq⟩
    simpa [hpEq] using hp
  · intro hp
    exact ⟨ZFSet.pair (s q) (s z), hp, rfl⟩

/-- The bounded body describing membership in a generated fiber. -/
def fiberGeneratedBody {n : Nat} (z : Fin n)
    (body : Delta0Formula (n + 1)) : Delta0Formula (n + 5) :=
  .conj
    (kuratowskiPairEqAt (componentPairIndex n)
      (componentLeftIndex n) (componentRightIndex n))
    (.conj
      (.eq (componentRightIndex n)
        z.castSucc.castSucc.castSucc.castSucc.castSucc)
      (Delta0Formula.rename (componentLastRename false n) body))

theorem satisfies_fiberGeneratedBody (z : Fin n)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n)
    (p leftBox left rightBox right : ZFSet.{u}) :
    Satisfies ZFMem (fiberGeneratedBody z body)
        (snoc (snoc (snoc (snoc (snoc s p) leftBox) left)
          rightBox) right) ↔
      p = ZFSet.pair left right ∧ right = s z ∧
        Satisfies ZFMem body (snoc s left) := by
  simp only [fiberGeneratedBody, Satisfies, satisfies_kuratowskiPairEqAt,
    componentPairIndex, componentLeftIndex, componentRightIndex,
    snoc_last, snoc_castSucc, Delta0Formula.satisfies_rename]
  rw [componentLastRename_assignment]
  rfl

/-- Eliminate a bounded quantifier over a fiber. -/
def fiberBoundAt {n : Nat} (x z : Fin n)
    (body : Delta0Formula (n + 1)) : Delta0Formula n :=
  withBoundedPairComponents x (fiberGeneratedBody z body)

@[simp]
theorem satisfies_fiberBoundAt {n : Nat} (x z : Fin n)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (fiberBoundAt x z body) s ↔
      ∃ q ∈ fiber (s x) (s z), Satisfies ZFMem body (snoc s q) := by
  simp only [fiberBoundAt, satisfies_withBoundedPairComponents,
    satisfies_fiberGeneratedBody]
  constructor
  · rintro ⟨p, hp, leftBox, hleftBox, left, hleft,
      rightBox, hrightBox, right, hright, hpEq, hrightEq, hbody⟩
    refine ⟨left, ?_, hbody⟩
    rw [mem_fiber_iff]
    simpa [hpEq, hrightEq] using hp
  · rintro ⟨left, hleftFiber, hbody⟩
    rw [mem_fiber_iff] at hleftFiber
    refine ⟨ZFSet.pair left (s z), hleftFiber,
      ({left} : ZFSet.{u}), ?_, left, ?_,
      ({left, s z} : ZFSet.{u}), ?_, s z, ?_, rfl, rfl, hbody⟩
    · simp [ZFSet.pair]
    · simp
    · simp [ZFSet.pair]
    · simp

/-- The simple-value specification for fibers. -/
noncomputable def fiberSpec : SimpleValueSpec.{u} where
  eval := fiber
  memAt := fiberMemAt
  eqAt := fiberEqAt
  boundAt := fiberBoundAt
  satisfies_memAt := by
    intro n q x z s
    exact satisfies_fiberMemAt q x z s
  satisfies_eqAt := by
    intro n out x z s
    exact satisfies_fiberEqAt out x z s
  satisfies_boundAt := by
    intro n x z body s
    exact satisfies_fiberBoundAt x z body s

theorem isSimpleSetFunction_fiber :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => fiber (s 0) (s 1)) := by
  simpa only [fiberSpec] using fiberSpec.{u}.isSimple

/-! ## F8 is a bounded image by the simple fiber operation -/

/-- Rename the coordinates used when eliminating a fiber witness. -/
def fiberElimRename {n : Nat} (x : Fin n) :
    Fin (2 + n) → Fin (n + 1) :=
  Fin.addCases
    (fun i : Fin 2 => Fin.cases x.castSucc
      (fun _ : Fin 1 => Fin.last n) i)
    (fun i : Fin n => i.castSucc)

theorem fiberElimRename_assignment (x : Fin n)
    (s : Tuple ZFSet.{u} n) (z : ZFSet.{u}) :
    (fun i => snoc s z (fiberElimRename x i)) =
      Fin.addCases ![s x, z] s := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    · simp [fiberElimRename]
    · change snoc s z (Fin.last n) = z
      simp
  · intro j
    simp [fiberElimRename]

/-- Eliminate a bounded quantifier over an F8 value. -/
noncomputable def f8BoundAt {n : Nat} (x y : Fin n)
    (body : Delta0Formula (n + 1)) : Delta0Formula n :=
  .boundedEx y
    (Delta0Formula.rename (fiberElimRename x)
      (eliminateSimpleLast.{u} isSimpleSetFunction_fiber body))

@[simp]
theorem satisfies_f8BoundAt {n : Nat} (x y : Fin n)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (f8BoundAt.{u} x y body) s ↔
      ∃ q ∈ F8 (s x) (s y), Satisfies ZFMem body (snoc s q) := by
  simp only [f8BoundAt, Satisfies, Delta0Formula.satisfies_rename]
  constructor
  · rintro ⟨z, hz, hbody⟩
    rw [fiberElimRename_assignment,
      satisfies_eliminateSimpleLast.{u}] at hbody
    refine ⟨fiber (s x) z, ?_, hbody⟩
    exact mem_F8_iff.mpr ⟨z, hz, rfl⟩
  · rintro ⟨q, hq, hbody⟩
    rcases mem_F8_iff.mp hq with ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [fiberElimRename_assignment,
      satisfies_eliminateSimpleLast.{u}]
    exact hbody

/-- The simple-value specification for F8. -/
noncomputable def f8Spec : SimpleValueSpec.{u} where
  eval := F8
  memAt := memOpAt 8
  eqAt := opEqAt 8
  boundAt := f8BoundAt.{u}
  satisfies_memAt := by
    intro n q x y s
    exact satisfies_memOpAt (8 : Fin 9) q x y s
  satisfies_eqAt := by
    intro n out x y s
    exact satisfies_opEqAt (8 : Fin 9) out x y s
  satisfies_boundAt := by
    intro n x y body s
    exact satisfies_f8BoundAt x y body s

theorem isSimpleSetFunction_F8 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F8 (s 0) (s 1)) := by
  simpa only [f8Spec] using f8Spec.{u}.isSimple

end Constructible.Godel
