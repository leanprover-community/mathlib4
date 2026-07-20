/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.SimpleGenerated

/-!
# Simplicity of the Gödel operations F3 and F4

This file instantiates the generic simple-function compiler for the two operations that extract
triple components from Kuratowski-pair encodings.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n : Nat}

/-- The two rudimentary operations whose values are sets of triples. -/
inductive TripleSetKind
  | f3
  | f4

namespace TripleSetKind

/-- The rudimentary-operation index of a triple-set operation. -/
def index : TripleSetKind → Fin 9
  | .f3 => 3
  | .f4 => 4

/-- Evaluate a triple-set operation. -/
noncomputable def eval (kind : TripleSetKind)
    (x y : ZFSet.{u}) : ZFSet.{u} :=
  op kind.index x y

@[simp] theorem eval_f3 (x y : ZFSet.{u}) :
    eval .f3 x y = F3 x y := by rfl

@[simp] theorem eval_f4 (x y : ZFSet.{u}) :
    eval .f4 x y = F4 x y := by rfl

end TripleSetKind

/-- The generated-element coordinate in the common F3/F4 layout. -/
def f34ZIndex (n : Nat) : Fin (n + 6) :=
  (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc

/-- The generated-pair coordinate in the common F3/F4 layout. -/
def f34PairIndex (n : Nat) : Fin (n + 6) :=
  (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc

/-- The left-component coordinate in the common F3/F4 layout. -/
def f34LeftIndex (n : Nat) : Fin (n + 6) :=
  (Fin.last (n + 3)).castSucc.castSucc

/-- The right-component coordinate in the common F3/F4 layout. -/
def f34RightIndex (n : Nat) : Fin (n + 6) :=
  Fin.last (n + 5)

/-- Send `[u,z,v]` (F3) or `[u,v,z]` (F4), followed by the old context,
into the six-coordinate bounded pair-component context. -/
def f34ElimRename (kind : TripleSetKind) (n : Nat) :
    Fin (3 + n) → Fin (n + 6) :=
  Fin.addCases
    (fun i : Fin 3 => Fin.cases (f34LeftIndex n)
      (fun j : Fin 2 =>
        match kind with
        | .f3 => Fin.cases (f34ZIndex n)
            (fun _ : Fin 1 => f34RightIndex n) j
        | .f4 => Fin.cases (f34RightIndex n)
            (fun _ : Fin 1 => f34ZIndex n) j) i)
    (fun i : Fin n =>
      i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem f34ElimRename_assignment (kind : TripleSetKind)
    (s : Tuple ZFSet.{u} n) (z p leftBox u rightBox v : ZFSet.{u}) :
    let extended :=
      snoc (snoc (snoc (snoc (snoc (snoc s z) p) leftBox) u)
        rightBox) v
    (fun i => extended (f34ElimRename kind n i)) =
      match kind with
      | .f3 => Fin.addCases ![u, z, v] s
      | .f4 => Fin.addCases ![u, v, z] s := by
  dsimp only
  cases kind with
  | f3 =>
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        fin_cases j
        · simp [f34ElimRename, f34LeftIndex]
        · change snoc (snoc (snoc (snoc (snoc (snoc s z) p)
            leftBox) u) rightBox) v (f34ZIndex n) = z
          simp [f34ZIndex]
        · change snoc (snoc (snoc (snoc (snoc (snoc s z) p)
            leftBox) u) rightBox) v (f34RightIndex n) = v
          simp [f34RightIndex]
      · intro j
        simp [f34ElimRename]
  | f4 =>
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        fin_cases j
        · simp [f34ElimRename, f34LeftIndex]
        · change snoc (snoc (snoc (snoc (snoc (snoc s z) p)
            leftBox) u) rightBox) v (f34RightIndex n) = v
          simp [f34RightIndex]
        · change snoc (snoc (snoc (snoc (snoc (snoc s z) p)
            leftBox) u) rightBox) v (f34ZIndex n) = z
          simp [f34ZIndex]
      · intro j
        simp [f34ElimRename]

/-- The bounded body describing one generated F3/F4 element. -/
noncomputable def f34GeneratedBody (kind : TripleSetKind) {n : Nat}
    (body : Delta0Formula (n + 1)) : Delta0Formula (n + 6) :=
  .conj
    (kuratowskiPairEqAt (f34PairIndex n)
      (f34LeftIndex n) (f34RightIndex n))
    (Delta0Formula.rename (f34ElimRename kind n)
      (eliminateSimpleLast.{u} isSimpleSetFunction_triple body))

theorem satisfies_f34GeneratedBody (kind : TripleSetKind)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n)
    (z p leftBox u rightBox v : ZFSet.{u}) :
    Satisfies ZFMem (f34GeneratedBody.{u} kind body)
        (snoc (snoc (snoc (snoc (snoc (snoc s z) p) leftBox) u)
          rightBox) v) ↔
      p = ZFSet.pair u v ∧
        match kind with
        | .f3 => Satisfies ZFMem body (snoc s (triple u z v))
        | .f4 => Satisfies ZFMem body (snoc s (triple u v z)) := by
  simp only [f34GeneratedBody, Satisfies,
    satisfies_kuratowskiPairEqAt, Delta0Formula.satisfies_rename,
    f34PairIndex, f34LeftIndex, f34RightIndex,
    snoc_last, snoc_castSucc]
  rw [f34ElimRename_assignment]
  cases kind
  · simp
  · simp

/-- Eliminate a bounded quantifier over an F3/F4 value. -/
noncomputable def f34BoundAt (kind : TripleSetKind) {n : Nat}
    (x y : Fin n) (body : Delta0Formula (n + 1)) :
    Delta0Formula n :=
  .boundedEx x
    (withBoundedPairComponents y.castSucc
      (f34GeneratedBody.{u} kind body))

@[simp]
theorem satisfies_f34BoundAt (kind : TripleSetKind) {n : Nat}
    (x y : Fin n) (body : Delta0Formula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (f34BoundAt.{u} kind x y body) s ↔
      ∃ q ∈ kind.eval (s x) (s y),
        Satisfies ZFMem body (snoc s q) := by
  cases kind with
  | f3 =>
      simp only [f34BoundAt, Satisfies,
        satisfies_withBoundedPairComponents, snoc_castSucc,
        satisfies_f34GeneratedBody, TripleSetKind.eval_f3]
      constructor
      · rintro ⟨z, hz, p, hp, leftBox, hleftBox, u, hu,
          rightBox, hrightBox, v, hv, hpEq, hbody⟩
        refine ⟨triple u z v, ?_, hbody⟩
        exact mem_F3_iff.mpr ⟨u, z, v, hz, by simpa [hpEq] using hp, rfl⟩
      · rintro ⟨q, hq, hbody⟩
        rcases mem_F3_iff.mp hq with ⟨u, z, v, hz, huv, rfl⟩
        refine ⟨z, hz, ZFSet.pair u v, huv,
          ({u} : ZFSet.{u}), ?_, u, ?_, ({u, v} : ZFSet.{u}), ?_,
          v, ?_, rfl, hbody⟩
        · simp [ZFSet.pair]
        · simp
        · simp [ZFSet.pair]
        · simp
  | f4 =>
      simp only [f34BoundAt, Satisfies,
        satisfies_withBoundedPairComponents, snoc_castSucc,
        satisfies_f34GeneratedBody, TripleSetKind.eval_f4]
      constructor
      · rintro ⟨z, hz, p, hp, leftBox, hleftBox, u, hu,
          rightBox, hrightBox, v, hv, hpEq, hbody⟩
        refine ⟨triple u v z, ?_, hbody⟩
        exact mem_F4_iff.mpr ⟨u, v, z, hz, by simpa [hpEq] using hp, rfl⟩
      · rintro ⟨q, hq, hbody⟩
        rcases mem_F4_iff.mp hq with ⟨u, v, z, hz, huv, rfl⟩
        refine ⟨z, hz, ZFSet.pair u v, huv,
          ({u} : ZFSet.{u}), ?_, u, ?_, ({u, v} : ZFSet.{u}), ?_,
          v, ?_, rfl, hbody⟩
        · simp [ZFSet.pair]
        · simp
        · simp [ZFSet.pair]
        · simp

/-- The simple-value specification for an F3/F4 operation. -/
noncomputable def f34Spec (kind : TripleSetKind) :
    SimpleValueSpec.{u} where
  eval := kind.eval
  memAt := memOpAt kind.index
  eqAt := opEqAt kind.index
  boundAt := f34BoundAt.{u} kind
  satisfies_memAt := by
    intro n q x y s
    exact satisfies_memOpAt kind.index q x y s
  satisfies_eqAt := by
    intro n out x y s
    exact satisfies_opEqAt kind.index out x y s
  satisfies_boundAt := by
    intro n x y body s
    exact satisfies_f34BoundAt kind x y body s

theorem isSimpleSetFunction_F3 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F3 (s 0) (s 1)) := by
  simpa only [f34Spec, TripleSetKind.eval_f3] using
    (f34Spec.{u} .f3).isSimple

theorem isSimpleSetFunction_F4 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F4 (s 0) (s 1)) := by
  simpa only [f34Spec, TripleSetKind.eval_f4] using
    (f34Spec.{u} .f4).isSimple

end Constructible.Godel
