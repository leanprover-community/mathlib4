/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Simple

/-!
# Strong-simple substitution

This file implements the substitution machinery for the inclusion
`godelDef U ⊆ DefZF U`.

The key point is that a membership section is not stable under composition.
This file develops complete elimination cases for set difference, internal
union, and unordered pairing, together with the generic composition and
simultaneous-substitution machinery used by the remaining primitive operations.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n m k : Nat}

/-- A set expression containing either a variable or one set difference. -/
inductive DiffExpr (n : Nat) where
  | var (i : Fin n)
  | diff (left right : Fin n)

namespace DiffExpr

/-- Ambient interpretation of a difference expression. -/
def eval (s : Tuple ZFSet.{u} n) : DiffExpr n → ZFSet.{u}
  | .var i => s i
  | .diff i j => s i \ s j

/-- Rename every variable occurring in a difference expression. -/
def rename (ρ : Fin n → Fin m) : DiffExpr n → DiffExpr m
  | .var i => .var (ρ i)
  | .diff i j => .diff (ρ i) (ρ j)

@[simp]
theorem eval_rename (ρ : Fin n → Fin m) (s : Tuple ZFSet.{u} m)
    (e : DiffExpr n) :
    eval s (rename ρ e) = eval (fun i => s (ρ i)) e := by
  cases e <;> rfl

end DiffExpr

/-- `a = x \ y`, expressed with quantifiers bounded by `a` and `x`. -/
def eqVarDiffAt {n : Nat} (a x y : Fin n) : Delta0Formula n :=
  .conj
    (.boundedAll a
      (.conj
        (.mem (Fin.last n) x.castSucc)
        (.neg (.mem (Fin.last n) y.castSucc))))
    (.boundedAll x
      (.imp
        (.neg (.mem (Fin.last n) y.castSucc))
        (.mem (Fin.last n) a.castSucc)))

@[simp]
theorem satisfies_eqVarDiffAt {n : Nat} (a x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqVarDiffAt a x y) s ↔ s a = s x \ s y := by
  simp only [eqVarDiffAt, Satisfies, satisfies_boundedAll, satisfies_imp,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sdiff]
    constructor
    · exact hsub z
    · rintro ⟨hzx, hnzy⟩
      exact hsup z hzx hnzy
  · intro h
    constructor
    · intro z hza
      rw [h] at hza
      exact ZFSet.mem_sdiff.mp hza
    · intro z hzx hnzy
      rw [h]
      exact ZFSet.mem_sdiff.mpr ⟨hzx, hnzy⟩

/-- `(x \ y) ∈ a`. -/
def memDiffVarAt {n : Nat} (x y a : Fin n) : Delta0Formula n :=
  .boundedEx a
    (eqVarDiffAt (Fin.last n) x.castSucc y.castSucc)

@[simp]
theorem satisfies_memDiffVarAt {n : Nat} (x y a : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memDiffVarAt x y a) s ↔ s x \ s y ∈ s a := by
  simp only [memDiffVarAt, Satisfies, satisfies_eqVarDiffAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨z, hza, hz⟩
    simpa [hz] using hza
  · intro h
    exact ⟨s x \ s y, h, rfl⟩

/-- Equality of two set differences. -/
def eqDiffDiffAt {n : Nat} (x y u v : Fin n) : Delta0Formula n :=
  .conj
    (.boundedAll x
      (.imp
        (.neg (.mem (Fin.last n) y.castSucc))
        (.conj
          (.mem (Fin.last n) u.castSucc)
          (.neg (.mem (Fin.last n) v.castSucc)))))
    (.boundedAll u
      (.imp
        (.neg (.mem (Fin.last n) v.castSucc))
        (.conj
          (.mem (Fin.last n) x.castSucc)
          (.neg (.mem (Fin.last n) y.castSucc)))))

@[simp]
theorem satisfies_eqDiffDiffAt {n : Nat} (x y u v : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqDiffDiffAt x y u v) s ↔
      s x \ s y = s u \ s v := by
  simp only [eqDiffDiffAt, Satisfies, satisfies_boundedAll, satisfies_imp,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hleft, hright⟩
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sdiff]
    constructor
    · rintro ⟨hzx, hnzy⟩
      exact hleft z hzx hnzy
    · rintro ⟨hzu, hnzv⟩
      exact hright z hzu hnzv
  · intro h
    constructor
    · intro z hzx hnzy
      have hz : z ∈ s x \ s y := ZFSet.mem_sdiff.mpr ⟨hzx, hnzy⟩
      rw [h] at hz
      exact ZFSet.mem_sdiff.mp hz
    · intro z hzu hnzv
      have hz : z ∈ s u \ s v := ZFSet.mem_sdiff.mpr ⟨hzu, hnzv⟩
      rw [← h] at hz
      exact ZFSet.mem_sdiff.mp hz

/-- Membership between two difference expressions. -/
def memDiffExpr {n : Nat} : DiffExpr n → DiffExpr n → Delta0Formula n
  | .var a, .var b => .mem a b
  | .var a, .diff x y => .conj (.mem a x) (.neg (.mem a y))
  | .diff x y, .var a => memDiffVarAt x y a
  | .diff x y, .diff u v =>
      .conj (memDiffVarAt x y u) (.neg (memDiffVarAt x y v))

/-- Equality between two difference expressions. -/
def eqDiffExpr {n : Nat} : DiffExpr n → DiffExpr n → Delta0Formula n
  | .var a, .var b => .eq a b
  | .var a, .diff x y => eqVarDiffAt a x y
  | .diff x y, .var a => eqVarDiffAt a x y
  | .diff x y, .diff u v => eqDiffDiffAt x y u v

@[simp]
theorem satisfies_memDiffExpr {n : Nat} (left right : DiffExpr n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memDiffExpr left right) s ↔
      left.eval s ∈ right.eval s := by
  cases left <;> cases right <;>
    simp [memDiffExpr, DiffExpr.eval, ZFSet.mem_sdiff]

@[simp]
theorem satisfies_eqDiffExpr {n : Nat} (left right : DiffExpr n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqDiffExpr left right) s ↔
      left.eval s = right.eval s := by
  cases left <;> cases right <;>
    simp [eqDiffExpr, DiffExpr.eval, eq_comm]

/-- Extend an expression substitution under a new bounded variable. -/
def liftDiffSubst {m n : Nat} (σ : Fin m → DiffExpr n) :
    Fin (m + 1) → DiffExpr (n + 1) :=
  Fin.lastCases (.var (Fin.last n))
    (fun i => (σ i).rename Fin.castSucc)

theorem eval_liftDiffSubst {m n : Nat} (σ : Fin m → DiffExpr n)
    (s : Tuple ZFSet.{u} n) (z : ZFSet.{u}) :
    (fun i => (liftDiffSubst σ i).eval (snoc s z)) =
      snoc (fun i => (σ i).eval s) z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [liftDiffSubst, DiffExpr.eval]
  · cases h : σ j <;> simp [liftDiffSubst, DiffExpr.eval, DiffExpr.rename, h]

/--
Eliminate a simultaneous substitution by variables and set differences from
an arbitrary intrinsically scoped bounded formula.
-/
def compileDiffSubst {m n : Nat} (σ : Fin m → DiffExpr n) :
    Delta0Formula m → Delta0Formula n
  | .mem i j => memDiffExpr (σ i) (σ j)
  | .eq i j => eqDiffExpr (σ i) (σ j)
  | .neg φ => .neg (compileDiffSubst σ φ)
  | .conj φ ψ => .conj (compileDiffSubst σ φ) (compileDiffSubst σ ψ)
  | .boundedEx i φ =>
      match σ i with
      | .var bound =>
          .boundedEx bound (compileDiffSubst (liftDiffSubst σ) φ)
      | .diff left right =>
          .boundedEx left
            (.conj
              (.neg (.mem (Fin.last n) right.castSucc))
              (compileDiffSubst (liftDiffSubst σ) φ))

@[simp]
theorem satisfies_compileDiffSubst {m n : Nat}
    (σ : Fin m → DiffExpr n) (φ : Delta0Formula m)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (compileDiffSubst σ φ) s ↔
      Satisfies ZFMem φ (fun i => (σ i).eval s) := by
  induction φ generalizing n with
  | mem i j => simp [compileDiffSubst]
  | eq i j => simp [compileDiffSubst]
  | neg φ ih => simp [compileDiffSubst, ih]
  | conj φ ψ ihφ ihψ => simp [compileDiffSubst, ihφ, ihψ]
  | boundedEx i φ ih =>
      cases h : σ i with
      | var bound =>
          simp only [compileDiffSubst, h, Satisfies]
          constructor
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [DiffExpr.eval, h] using hz
            · rw [ih] at hφ
              simpa only [eval_liftDiffSubst] using hφ
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [DiffExpr.eval, h] using hz
            · rw [ih]
              simpa only [eval_liftDiffSubst] using hφ
      | diff left right =>
          simp only [compileDiffSubst, h, Satisfies]
          constructor
          · rintro ⟨z, hzleft, hnzright, hφ⟩
            have hnzright' : z ∉ s right := by
              simpa only [snoc_last, snoc_castSucc] using hnzright
            refine ⟨z, ?_, ?_⟩
            · simpa [DiffExpr.eval, h, ZFSet.mem_sdiff] using
                (show z ∈ s left ∧ z ∉ s right from ⟨hzleft, hnzright'⟩)
            · rw [ih] at hφ
              simpa only [eval_liftDiffSubst] using hφ
          · rintro ⟨z, hz, hφ⟩
            have hz' : z ∈ s left ∧ z ∉ s right := by
              simpa [DiffExpr.eval, h, ZFSet.mem_sdiff] using hz
            refine ⟨z, hz'.1, ?_, ?_⟩
            · simpa only [snoc_last, snoc_castSucc] using hz'.2
            rw [ih]
            simpa only [eval_liftDiffSubst] using hφ

/--
Jensen simplicity for a set-valued function: substituting its value into any
bounded context, while retaining any finite tuple of extra parameters, can be
eliminated to another bounded formula.
-/
def IsSimpleSetFunction {n : Nat}
    (f : Tuple ZFSet.{u} n → ZFSet.{u}) : Prop :=
  ∀ k : Nat, ∀ φ : Delta0Formula (1 + k),
    ∃ ψ : Delta0Formula (n + k),
      ∀ (args : Tuple ZFSet.{u} n) (extra : Tuple ZFSet.{u} k),
        Satisfies ZFMem ψ (Fin.addCases args extra) ↔
          Satisfies ZFMem φ (Fin.addCases (fun _ => f args) extra)

/-- Substitution used to eliminate `x \ y` from a bounded context. -/
def diffContextSubst (k : Nat) : Fin (1 + k) → DiffExpr (2 + k) :=
  Fin.addCases
    (fun _ => .diff (Fin.castAdd k (0 : Fin 2)) (Fin.castAdd k (1 : Fin 2)))
    (fun i => .var (Fin.natAdd 2 i))

theorem eval_diffContextSubst (x y : ZFSet.{u})
    (extra : Tuple ZFSet.{u} k) :
    (fun i => (diffContextSubst k i).eval (Fin.addCases ![x, y] extra)) =
      Fin.addCases (fun _ : Fin 1 => x \ y) extra := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    rfl
  · intro j
    simp [diffContextSubst, DiffExpr.eval]

/-- The primitive set-difference function is simple in Jensen's strong sense. -/
theorem isSimpleSetFunction_sdiff :
    IsSimpleSetFunction (fun s : Tuple ZFSet.{u} 2 => s 0 \ s 1) := by
  intro k φ
  refine ⟨compileDiffSubst (diffContextSubst k) φ, ?_⟩
  intro args extra
  rw [satisfies_compileDiffSubst]
  have hargs : args = ![args 0, args 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hargs, eval_diffContextSubst]
  rfl

/-! ## A second complete case: internal union (`F₅`) -/

/-- A set expression containing either a variable or one internal union. -/
inductive UnionExpr (n : Nat) where
  | var (i : Fin n)
  | sUnion (set : Fin n)

namespace UnionExpr

/-- Evaluate an internal-union expression in an assignment. -/
def eval (s : Tuple ZFSet.{u} n) : UnionExpr n → ZFSet.{u}
  | .var i => s i
  | .sUnion i => ZFSet.sUnion (s i)

/-- Rename the variables in an internal-union expression. -/
def rename (ρ : Fin n → Fin m) : UnionExpr n → UnionExpr m
  | .var i => .var (ρ i)
  | .sUnion i => .sUnion (ρ i)

@[simp]
theorem eval_rename (ρ : Fin n → Fin m) (s : Tuple ZFSet.{u} m)
    (e : UnionExpr n) :
    eval s (rename ρ e) = eval (fun i => s (ρ i)) e := by
  cases e <;> rfl

end UnionExpr

/-- `a = ⋃ x`, with both containments written using bounded quantifiers. -/
def eqVarUnionAt {n : Nat} (a x : Fin n) : Delta0Formula n :=
  .conj
    (.boundedAll a
      (.boundedEx x.castSucc
        (.mem (Fin.last n).castSucc (Fin.last (n + 1)))))
    (.boundedAll x
      (.boundedAll (Fin.last n)
        (.mem (Fin.last (n + 1)) a.castSucc.castSucc)))

@[simp]
theorem satisfies_eqVarUnionAt {n : Nat} (a x : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqVarUnionAt a x) s ↔
      s a = ZFSet.sUnion (s x) := by
  simp only [eqVarUnionAt, Satisfies, satisfies_boundedAll,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hleft, hright⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sUnion]
    constructor
    · intro hza
      rcases hleft z hza with ⟨w, hwx, hzw⟩
      exact ⟨w, hwx, hzw⟩
    · rintro ⟨w, hwx, hzw⟩
      exact hright w hwx z hzw
  · intro h
    constructor
    · intro z hza
      rw [h] at hza
      exact ZFSet.mem_sUnion.mp hza
    · intro w hwx z hzw
      rw [h]
      exact ZFSet.mem_sUnion.mpr ⟨w, hwx, hzw⟩

/-- `(⋃x) ∈ a`. -/
def memUnionVarAt {n : Nat} (x a : Fin n) : Delta0Formula n :=
  .boundedEx a
    (eqVarUnionAt (Fin.last n) x.castSucc)

@[simp]
theorem satisfies_memUnionVarAt {n : Nat} (x a : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memUnionVarAt x a) s ↔
      ZFSet.sUnion (s x) ∈ s a := by
  simp only [memUnionVarAt, Satisfies, satisfies_eqVarUnionAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨z, hza, hz⟩
    simpa [hz] using hza
  · intro h
    exact ⟨ZFSet.sUnion (s x), h, rfl⟩

/-- Equality of two internal unions. -/
def eqUnionUnionAt {n : Nat} (x y : Fin n) : Delta0Formula n :=
  .conj
    (.boundedAll x
      (.boundedAll (Fin.last n)
        (.boundedEx y.castSucc.castSucc
          (.mem (Fin.last (n + 1)).castSucc (Fin.last (n + 2))))))
    (.boundedAll y
      (.boundedAll (Fin.last n)
        (.boundedEx x.castSucc.castSucc
          (.mem (Fin.last (n + 1)).castSucc (Fin.last (n + 2))))))

@[simp]
theorem satisfies_eqUnionUnionAt {n : Nat} (x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqUnionUnionAt x y) s ↔
      ZFSet.sUnion (s x) = ZFSet.sUnion (s y) := by
  simp only [eqUnionUnionAt, Satisfies, satisfies_boundedAll,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hxy, hyx⟩
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sUnion]
    constructor
    · rintro ⟨w, hwx, hzw⟩
      rcases hxy w hwx z hzw with ⟨v, hvy, hzv⟩
      exact ⟨v, hvy, hzv⟩
    · rintro ⟨v, hvy, hzv⟩
      rcases hyx v hvy z hzv with ⟨w, hwx, hzw⟩
      exact ⟨w, hwx, hzw⟩
  · intro h
    constructor
    · intro w hwx z hzw
      have hz : z ∈ ZFSet.sUnion (s x) :=
        ZFSet.mem_sUnion.mpr ⟨w, hwx, hzw⟩
      rw [h] at hz
      exact ZFSet.mem_sUnion.mp hz
    · intro v hvy z hzv
      have hz : z ∈ ZFSet.sUnion (s y) :=
        ZFSet.mem_sUnion.mpr ⟨v, hvy, hzv⟩
      rw [← h] at hz
      exact ZFSet.mem_sUnion.mp hz

/-- Compile membership between two internal-union expressions. -/
def memUnionExpr {n : Nat} : UnionExpr n → UnionExpr n → Delta0Formula n
  | .var a, .var b => .mem a b
  | .var a, .sUnion x =>
      .boundedEx x (.mem a.castSucc (Fin.last n))
  | .sUnion x, .var a => memUnionVarAt x a
  | .sUnion x, .sUnion y =>
      .boundedEx y (memUnionVarAt x.castSucc (Fin.last n))

/-- Compile equality between two internal-union expressions. -/
def eqUnionExpr {n : Nat} : UnionExpr n → UnionExpr n → Delta0Formula n
  | .var a, .var b => .eq a b
  | .var a, .sUnion x => eqVarUnionAt a x
  | .sUnion x, .var a => eqVarUnionAt a x
  | .sUnion x, .sUnion y => eqUnionUnionAt x y

@[simp]
theorem satisfies_memUnionExpr {n : Nat} (left right : UnionExpr n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memUnionExpr left right) s ↔
      left.eval s ∈ right.eval s := by
  cases left <;> cases right <;>
    simp [memUnionExpr, UnionExpr.eval, ZFSet.mem_sUnion]

@[simp]
theorem satisfies_eqUnionExpr {n : Nat} (left right : UnionExpr n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqUnionExpr left right) s ↔
      left.eval s = right.eval s := by
  cases left <;> cases right <;>
    simp [eqUnionExpr, UnionExpr.eval, eq_comm]

/-- Lift an internal-union substitution through one binder. -/
def liftUnionSubst {m n : Nat} (σ : Fin m → UnionExpr n) :
    Fin (m + 1) → UnionExpr (n + 1) :=
  Fin.lastCases (.var (Fin.last n))
    (fun i => (σ i).rename Fin.castSucc)

/-- Lift under the two target binders used to enumerate `z ∈ w ∈ x`. -/
def liftUnionDoubleSubst {m n : Nat} (σ : Fin m → UnionExpr n) :
    Fin (m + 1) → UnionExpr (n + 2) :=
  Fin.lastCases (.var (Fin.last (n + 1)))
    (fun i => (σ i).rename (fun j => j.castSucc.castSucc))

theorem eval_liftUnionSubst {m n : Nat} (σ : Fin m → UnionExpr n)
    (s : Tuple ZFSet.{u} n) (z : ZFSet.{u}) :
    (fun i => (liftUnionSubst σ i).eval (snoc s z)) =
      snoc (fun i => (σ i).eval s) z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [liftUnionSubst, UnionExpr.eval]
  · cases h : σ j <;> simp [liftUnionSubst, UnionExpr.eval,
      UnionExpr.rename, h]

theorem eval_liftUnionDoubleSubst {m n : Nat}
    (σ : Fin m → UnionExpr n) (s : Tuple ZFSet.{u} n)
    (w z : ZFSet.{u}) :
    (fun i => (liftUnionDoubleSubst σ i).eval (snoc (snoc s w) z)) =
      snoc (fun i => (σ i).eval s) z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [liftUnionDoubleSubst, UnionExpr.eval]
  · cases h : σ j <;> simp [liftUnionDoubleSubst, UnionExpr.eval,
      UnionExpr.rename, h]

/-- Eliminate variables/internal-union expressions from a bounded formula. -/
def compileUnionSubst {m n : Nat} (σ : Fin m → UnionExpr n) :
    Delta0Formula m → Delta0Formula n
  | .mem i j => memUnionExpr (σ i) (σ j)
  | .eq i j => eqUnionExpr (σ i) (σ j)
  | .neg φ => .neg (compileUnionSubst σ φ)
  | .conj φ ψ => .conj (compileUnionSubst σ φ) (compileUnionSubst σ ψ)
  | .boundedEx i φ =>
      match σ i with
      | .var bound =>
          .boundedEx bound (compileUnionSubst (liftUnionSubst σ) φ)
      | .sUnion x =>
          .boundedEx x
            (.boundedEx (Fin.last n)
              (compileUnionSubst (liftUnionDoubleSubst σ) φ))

@[simp]
theorem satisfies_compileUnionSubst {m n : Nat}
    (σ : Fin m → UnionExpr n) (φ : Delta0Formula m)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (compileUnionSubst σ φ) s ↔
      Satisfies ZFMem φ (fun i => (σ i).eval s) := by
  induction φ generalizing n with
  | mem i j => simp [compileUnionSubst]
  | eq i j => simp [compileUnionSubst]
  | neg φ ih => simp [compileUnionSubst, ih]
  | conj φ ψ ihφ ihψ => simp [compileUnionSubst, ihφ, ihψ]
  | boundedEx i φ ih =>
      cases h : σ i with
      | var bound =>
          simp only [compileUnionSubst, h, Satisfies]
          constructor
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [UnionExpr.eval, h] using hz
            · rw [ih] at hφ
              simpa only [eval_liftUnionSubst] using hφ
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [UnionExpr.eval, h] using hz
            · rw [ih]
              simpa only [eval_liftUnionSubst] using hφ
      | sUnion x =>
          simp only [compileUnionSubst, h, Satisfies]
          constructor
          · rintro ⟨w, hwx, z, hzw, hφ⟩
            have hzw' : z ∈ w := by
              simpa only [snoc_last] using hzw
            refine ⟨z, ?_, ?_⟩
            · simpa [UnionExpr.eval, h, ZFSet.mem_sUnion] using
                (show ∃ w, w ∈ s x ∧ z ∈ w from ⟨w, hwx, hzw'⟩)
            · rw [ih] at hφ
              simpa only [eval_liftUnionDoubleSubst] using hφ
          · rintro ⟨z, hz, hφ⟩
            have hz' : ∃ w, w ∈ s x ∧ z ∈ w := by
              simpa [UnionExpr.eval, h, ZFSet.mem_sUnion] using hz
            rcases hz' with ⟨w, hwx, hzw⟩
            refine ⟨w, hwx, z, ?_, ?_⟩
            · simpa only [snoc_last] using hzw
            · rw [ih]
              simpa only [eval_liftUnionDoubleSubst] using hφ

/-- The substitution placing one internal union before the remaining context. -/
def unionContextSubst (k : Nat) : Fin (1 + k) → UnionExpr (1 + k) :=
  Fin.addCases
    (fun _ => .sUnion (Fin.castAdd k (0 : Fin 1)))
    (fun i => .var (Fin.natAdd 1 i))

theorem eval_unionContextSubst (x : ZFSet.{u})
    (extra : Tuple ZFSet.{u} k) :
    (fun i => (unionContextSubst k i).eval
      (Fin.addCases (fun _ : Fin 1 => x) extra)) =
      Fin.addCases (fun _ : Fin 1 => ZFSet.sUnion x) extra := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    rfl
  · intro j
    simp [unionContextSubst, UnionExpr.eval]

/-- The primitive internal-union function (`F₅`) is Jensen-simple. -/
theorem isSimpleSetFunction_sUnion :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 1 => ZFSet.sUnion (s 0)) := by
  intro k φ
  refine ⟨compileUnionSubst (unionContextSubst k) φ, ?_⟩
  intro args extra
  rw [satisfies_compileUnionSubst]
  have hargs : args = (fun _ : Fin 1 => args 0) := by
    funext i
    fin_cases i
    rfl
  rw [hargs, eval_unionContextSubst]

/-! ## A third complete case: unordered pairing (`F₀`) -/

/-- An expression that is a variable or an unordered pair of variables. -/
inductive PairExpr (n : Nat) where
  | var (i : Fin n)
  | pair (left right : Fin n)

namespace PairExpr

/-- Evaluate an unordered-pair expression in an assignment. -/
def eval (s : Tuple ZFSet.{u} n) : PairExpr n → ZFSet.{u}
  | .var i => s i
  | .pair i j => ({s i, s j} : ZFSet.{u})

end PairExpr

/-- `a = {x,y}`. -/
def eqVarPairAt {n : Nat} (a x y : Fin n) : Delta0Formula n :=
  .conj (.mem x a)
    (.conj (.mem y a)
      (.boundedAll a
        (.disj
          (.eq (Fin.last n) x.castSucc)
          (.eq (Fin.last n) y.castSucc))))

@[simp]
theorem satisfies_eqVarPairAt {n : Nat} (a x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqVarPairAt a x y) s ↔
      s a = ({s x, s y} : ZFSet.{u}) := by
  simpa only [eqVarPairAt, unorderedPairEqAt] using
    (satisfies_unorderedPairEqAt a x y s)

/-- A bounded formula asserting that an unordered pair belongs to a variable. -/
def memPairVarAt {n : Nat} (x y a : Fin n) : Delta0Formula n :=
  .boundedEx a
    (eqVarPairAt (Fin.last n) x.castSucc y.castSucc)

@[simp]
theorem satisfies_memPairVarAt {n : Nat} (x y a : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memPairVarAt x y a) s ↔
      ({s x, s y} : ZFSet.{u}) ∈ s a := by
  simp only [memPairVarAt, Satisfies, satisfies_eqVarPairAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨z, hza, hz⟩
    simpa [hz] using hza
  · intro h
    exact ⟨({s x, s y} : ZFSet.{u}), h, rfl⟩

/-- A bounded formula asserting equality of two unordered pairs. -/
def eqPairPairAt {n : Nat} (x y u v : Fin n) : Delta0Formula n :=
  .conj
    (.conj (.disj (.eq x u) (.eq x v)) (.disj (.eq y u) (.eq y v)))
    (.conj (.disj (.eq u x) (.eq u y)) (.disj (.eq v x) (.eq v y)))

@[simp]
theorem satisfies_eqPairPairAt {n : Nat} (x y u v : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqPairPairAt x y u v) s ↔
      ({s x, s y} : ZFSet.{u}) = ({s u, s v} : ZFSet.{u}) := by
  simp only [eqPairPairAt, Satisfies, satisfies_disj]
  constructor
  · rintro ⟨⟨hxu, hyv⟩, ⟨hux, hvx⟩⟩
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_pair]
    constructor
    · rintro (rfl | rfl)
      · exact hxu
      · exact hyv
    · rintro (rfl | rfl)
      · exact hux
      · exact hvx
  · intro h
    have hx : s x ∈ ({s u, s v} : ZFSet.{u}) := by
      rw [← h]
      simp
    have hy : s y ∈ ({s u, s v} : ZFSet.{u}) := by
      rw [← h]
      simp
    have hu : s u ∈ ({s x, s y} : ZFSet.{u}) := by
      rw [h]
      simp
    have hv : s v ∈ ({s x, s y} : ZFSet.{u}) := by
      rw [h]
      simp
    exact ⟨⟨ZFSet.mem_pair.mp hx, ZFSet.mem_pair.mp hy⟩,
      ⟨ZFSet.mem_pair.mp hu, ZFSet.mem_pair.mp hv⟩⟩

/-- Compile membership between unordered-pair expressions. -/
def memPairExpr {n : Nat} : PairExpr n → PairExpr n → Delta0Formula n
  | .var a, .var b => .mem a b
  | .var a, .pair x y => .disj (.eq a x) (.eq a y)
  | .pair x y, .var a => memPairVarAt x y a
  | .pair x y, .pair u v =>
      .disj (eqVarPairAt u x y) (eqVarPairAt v x y)

/-- Compile equality between unordered-pair expressions. -/
def eqPairExpr {n : Nat} : PairExpr n → PairExpr n → Delta0Formula n
  | .var a, .var b => .eq a b
  | .var a, .pair x y => eqVarPairAt a x y
  | .pair x y, .var a => eqVarPairAt a x y
  | .pair x y, .pair u v => eqPairPairAt x y u v

@[simp]
theorem satisfies_memPairExpr {n : Nat} (left right : PairExpr n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memPairExpr left right) s ↔
      left.eval s ∈ right.eval s := by
  cases left <;> cases right <;>
    simp [memPairExpr, PairExpr.eval, eq_comm]

@[simp]
theorem satisfies_eqPairExpr {n : Nat} (left right : PairExpr n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqPairExpr left right) s ↔
      left.eval s = right.eval s := by
  cases left <;> cases right <;>
    simp [eqPairExpr, PairExpr.eval, eq_comm]

/-- Replace the new source binder by an already available target variable. -/
def extendPairChoice {m n : Nat} (σ : Fin m → PairExpr n)
    (choice : Fin n) : Fin (m + 1) → PairExpr n :=
  Fin.lastCases (.var choice) σ

theorem eval_extendPairChoice {m n : Nat} (σ : Fin m → PairExpr n)
    (choice : Fin n) (s : Tuple ZFSet.{u} n) :
    (fun i => (extendPairChoice σ choice i).eval s) =
      snoc (fun i => (σ i).eval s) (s choice) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [extendPairChoice, PairExpr.eval]

/-- Lift an unordered-pair substitution through one binder. -/
def liftPairSubst {m n : Nat} (σ : Fin m → PairExpr n) :
    Fin (m + 1) → PairExpr (n + 1) :=
  Fin.lastCases (.var (Fin.last n))
    (fun j => match σ j with
      | .var a => .var a.castSucc
      | .pair a b => .pair a.castSucc b.castSucc)

/-- Eliminate variables/unordered-pair expressions from a bounded formula. -/
def compilePairSubst {m n : Nat} (σ : Fin m → PairExpr n) :
    Delta0Formula m → Delta0Formula n
  | .mem i j => memPairExpr (σ i) (σ j)
  | .eq i j => eqPairExpr (σ i) (σ j)
  | .neg φ => .neg (compilePairSubst σ φ)
  | .conj φ ψ => .conj (compilePairSubst σ φ) (compilePairSubst σ ψ)
  | .boundedEx i φ =>
      match σ i with
      | .var bound =>
          .boundedEx bound
            (compilePairSubst (liftPairSubst σ) φ)
      | .pair left right =>
          .disj
            (compilePairSubst (extendPairChoice σ left) φ)
            (compilePairSubst (extendPairChoice σ right) φ)

theorem eval_liftPairSubst {m n : Nat} (σ : Fin m → PairExpr n)
    (s : Tuple ZFSet.{u} n) (z : ZFSet.{u}) :
    (fun i => (liftPairSubst σ i).eval (snoc s z)) =
      snoc (fun i => (σ i).eval s) z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [liftPairSubst, PairExpr.eval]
  · cases h : σ j <;> simp [liftPairSubst, PairExpr.eval, h]

@[simp]
theorem satisfies_compilePairSubst {m n : Nat}
    (σ : Fin m → PairExpr n) (φ : Delta0Formula m)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (compilePairSubst σ φ) s ↔
      Satisfies ZFMem φ (fun i => (σ i).eval s) := by
  induction φ generalizing n with
  | mem i j => simp [compilePairSubst]
  | eq i j => simp [compilePairSubst]
  | neg φ ih => simp [compilePairSubst, ih]
  | conj φ ψ ihφ ihψ => simp [compilePairSubst, ihφ, ihψ]
  | boundedEx i φ ih =>
      cases h : σ i with
      | var bound =>
          simp only [compilePairSubst, h, Satisfies]
          constructor
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [PairExpr.eval, h] using hz
            · rw [ih] at hφ
              simpa only [eval_liftPairSubst] using hφ
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [PairExpr.eval, h] using hz
            · rw [ih]
              simpa only [eval_liftPairSubst] using hφ
      | pair left right =>
          simp only [compilePairSubst, h, satisfies_disj]
          rw [ih, ih, eval_extendPairChoice, eval_extendPairChoice]
          simp only [PairExpr.eval, h, ZFSet.mem_pair, Satisfies]
          constructor
          · intro hs
            rcases hs with hs | hs
            · exact ⟨s left, Or.inl rfl, hs⟩
            · exact ⟨s right, Or.inr rfl, hs⟩
          · rintro ⟨z, hz, hφ⟩
            rcases hz with rfl | rfl
            · exact Or.inl hφ
            · exact Or.inr hφ

/-- The substitution placing one unordered pair before the remaining context. -/
def pairContextSubst (k : Nat) : Fin (1 + k) → PairExpr (2 + k) :=
  Fin.addCases
    (fun _ => .pair (Fin.castAdd k (0 : Fin 2)) (Fin.castAdd k (1 : Fin 2)))
    (fun i => .var (Fin.natAdd 2 i))

theorem eval_pairContextSubst (x y : ZFSet.{u})
    (extra : Tuple ZFSet.{u} k) :
    (fun i => (pairContextSubst k i).eval (Fin.addCases ![x, y] extra)) =
      Fin.addCases (fun _ : Fin 1 => ({x, y} : ZFSet.{u})) extra := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    rfl
  · intro j
    simp [pairContextSubst, PairExpr.eval]

/-- The primitive unordered-pairing function (`F₀`) is Jensen-simple. -/
theorem isSimpleSetFunction_pair :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => ({s 0, s 1} : ZFSet.{u})) := by
  intro k φ
  refine ⟨compilePairSubst (pairContextSubst k) φ, ?_⟩
  intro args extra
  rw [satisfies_compilePairSubst]
  have hargs : args = ![args 0, args 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hargs, eval_pairContextSubst]
  rfl

/-! ## Checked composition -/

/-- Jensen-simple functions are closed under unary outer composition. -/
theorem IsSimpleSetFunction.compUnary {n : Nat}
    {outer : Tuple ZFSet.{u} 1 → ZFSet.{u}}
    {inner : Tuple ZFSet.{u} n → ZFSet.{u}}
    (hOuter : IsSimpleSetFunction outer)
    (hInner : IsSimpleSetFunction inner) :
    IsSimpleSetFunction (fun args => outer (fun _ => inner args)) := by
  intro k φ
  rcases hOuter k φ with ⟨middle, hmiddle⟩
  rcases hInner k middle with ⟨result, hresult⟩
  refine ⟨result, ?_⟩
  intro args extra
  exact (hresult args extra).trans
    (hmiddle (fun _ : Fin 1 => inner args) extra)

/--
The formerly problematic composition `⋃{x,y}` is simple without quantifying
over the external intermediate set `{x,y}`.
-/
theorem isSimpleSetFunction_unionPair :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => ZFSet.sUnion ({s 0, s 1} : ZFSet.{u})) := by
  have h := isSimpleSetFunction_sUnion.compUnary isSimpleSetFunction_pair
  simpa using h

/-! ## Eliminating the distinguished universe constant -/

namespace EraseUniverse

/-- A uniformly true formula, including at arity zero. -/
def truth (n : Nat) : FOFormula n :=
  .neg (.ex (.neg (.eq (Fin.last n) (Fin.last n))))

/-- A uniformly false formula, including at arity zero. -/
def falsity (n : Nat) : FOFormula n :=
  .ex (.neg (.eq (Fin.last n) (Fin.last n)))

@[simp]
theorem satisfies_truth {A : Type u} (E : A → A → Prop)
    (s : Tuple A n) : FOFormula.Satisfies E (truth n) s := by
  simp [truth]

@[simp]
theorem not_satisfies_falsity {A : Type u} (E : A → A → Prop)
    (s : Tuple A n) : ¬FOFormula.Satisfies E (falsity n) s := by
  simp [falsity]

/--
Remove coordinate zero, interpreted as the distinguished constant `U`.
All other coordinates are shifted down by one.  A bounded quantifier over `U`
becomes an ordinary first-order quantifier over the carrier structure.
-/
def formula : {n : Nat} → Delta0Formula (n + 1) → FOFormula n
  | n, .mem i j =>
      Fin.cases (falsity n)
        (fun i' => Fin.cases (truth n) (fun j' => .mem i' j') j) i
  | n, .eq i j =>
      Fin.cases
        (Fin.cases (truth n) (fun _ => falsity n) j)
        (fun i' => Fin.cases (falsity n) (fun j' => .eq i' j') j) i
  | _, .neg φ => .neg (formula φ)
  | _, .conj φ ψ => .conj (formula φ) (formula ψ)
  | _, .boundedEx i φ =>
      Fin.cases (.ex (formula φ))
        (fun i' => FOFormula.boundedEx i' (formula φ)) i

theorem universe_not_mem_carrier {U : ZFSet.{u}} (hU : U.IsTransitive)
    (x : ZFCarrier U) : U ∉ x.1 := by
  intro h
  exact ZFSet.mem_irrefl U (hU.mem_trans h x.2)

theorem universe_ne_carrier {U : ZFSet.{u}} (_hU : U.IsTransitive)
    (x : ZFCarrier U) : U ≠ x.1 := by
  intro h
  let xv : ZFSet.{u} := x.1
  have hxU : xv ∈ U := x.2
  have heq : U = xv := h
  have hself : xv ∈ xv := by
    simpa only [heq] using hxU
  exact ZFSet.mem_irrefl xv hself

@[simp]
theorem satisfies_formula {U : ZFSet.{u}} (hU : U.IsTransitive)
    (φ : Delta0Formula (n + 1)) (s : Tuple (ZFCarrier U) n) :
    FOFormula.Satisfies (zfCarrierMem U) (formula φ) s ↔
      Satisfies ZFMem φ (tupleCons U (Delta0Formula.val s)) := by
  fun_induction formula φ with
  | case1 _n i j =>
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simpa [falsity] using ZFSet.mem_irrefl U
        · simp [falsity, universe_not_mem_carrier hU]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [truth]
        · rfl
  | case2 _n i j =>
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [truth]
        · simp [falsity, universe_ne_carrier hU]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [falsity, universe_ne_carrier hU, eq_comm]
        · simp only [Fin.cases_succ, FOFormula.Satisfies, Satisfies,
            tupleCons_succ]
          exact Subtype.coe_injective.eq_iff.symm
  | case3 _n φ ih =>
      simpa [formula] using not_congr (ih s)
  | case4 _n φ ψ ihφ ihψ =>
      exact and_congr (ihφ s) (ihψ s)
  | case5 _n i φ ih =>
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp only [Satisfies, tupleCons_zero]
        constructor
        · rintro ⟨x, hx⟩
          refine ⟨x.1, x.2, ?_⟩
          have hx' := (ih (snoc s x)).mp hx
          simpa only [Delta0Formula.val_snoc, snoc_tupleCons] using hx'
        · rintro ⟨x, hxU, hx⟩
          refine ⟨⟨x, hxU⟩, ?_⟩
          apply (ih (snoc s ⟨x, hxU⟩)).mpr
          simpa only [Delta0Formula.val_snoc, snoc_tupleCons] using hx
      · simp only [Satisfies, tupleCons_succ]
        constructor
        · rintro ⟨x, hxs, hx⟩
          have hxs' : x.1 ∈ (s i').1 := by
            simpa only [FOFormula.Satisfies, zfCarrierMem,
              snoc_last, snoc_castSucc] using hxs
          refine ⟨x.1, hxs', ?_⟩
          have hx' := (ih (snoc s x)).mp hx
          simpa only [Delta0Formula.val_snoc, snoc_tupleCons] using hx'
        · rintro ⟨x, hxs, hx⟩
          have hxU : x ∈ U := hU.mem_trans hxs (s i').2
          let x' : ZFCarrier U := ⟨x, hxU⟩
          refine ⟨x', ?_, ?_⟩
          · simpa only [FOFormula.Satisfies, zfCarrierMem,
              Delta0Formula.val_apply, snoc_last, snoc_castSucc] using hxs
          apply (ih (snoc s x')).mpr
          simpa only [Delta0Formula.val_snoc, snoc_tupleCons] using hx

end EraseUniverse

@[simp]
theorem finAddCases_one_eq_snoc {A : Type u} {n : Nat}
    (s : Tuple A n) (x : A) :
    Fin.addCases s (fun _ : Fin 1 => x) = snoc s x := by
  funext i
  by_cases h : i.val < n
  · have hi : i = (i.castLT h).castSucc := Fin.ext rfl
    have hr : snoc s x i = s (i.castLT h) := by
      exact (congrArg (snoc s x) hi).trans (snoc_castSucc _ _ _)
    rw [hr]
    simp [Fin.addCases, h]
  · have hi : i = Fin.last n := Fin.eq_last_of_not_lt h
    have hr : snoc s x i = x := by
      exact (congrArg (snoc s x) hi).trans (snoc_last _ _)
    rw [hr]
    simp [Fin.addCases, h]

/--
The reusable final bridge for the hard inclusion.  Once a function is known
to be Jensen-simple, applying it to the distinguished argument `U` followed
by genuine parameters from `U` gives a member of `DefZF U`, provided its value
is a subset of `U`.
-/
theorem IsSimpleSetFunction.mem_DefZF_withUniverse {n : Nat}
    {f : Tuple ZFSet.{u} (n + 1) → ZFSet.{u}}
    (hf : IsSimpleSetFunction f) {U : ZFSet.{u}}
    (hU : U.IsTransitive) (params : Tuple (ZFCarrier U) n)
    (hsub : f (tupleCons U (Delta0Formula.val params)) ⊆ U) :
    f (tupleCons U (Delta0Formula.val params)) ∈ DefZF U := by
  let membership : Delta0Formula (1 + 1) := .mem 1 0
  rcases hf 1 membership with ⟨ψ, hψ⟩
  rw [mem_DefZF_iff_exists_satisfies]
  refine ⟨hsub, n, params, EraseUniverse.formula ψ, ?_⟩
  intro q
  rw [EraseUniverse.satisfies_formula hU]
  have hassign :
      tupleCons U (Delta0Formula.val (snoc params q)) =
        Fin.addCases (tupleCons U (Delta0Formula.val params))
          (fun _ : Fin 1 => q.1) := by
    rw [Delta0Formula.val_snoc, finAddCases_one_eq_snoc,
      snoc_tupleCons]
  rw [hassign]
  have hs := hψ (tupleCons U (Delta0Formula.val params))
    (fun _ : Fin 1 => q.1)
  change
    q.1 ∈ f (tupleCons U (Delta0Formula.val params)) ↔
      Satisfies ZFMem ψ
        (Fin.addCases (tupleCons U (Delta0Formula.val params))
          (fun _ : Fin 1 => q.1))
  exact hs.symm

private def singletonContextSubst (k : Nat) : Fin (1 + k) → PairExpr (1 + k) :=
  Fin.addCases
    (fun _ => .pair (Fin.castAdd k (0 : Fin 1))
      (Fin.castAdd k (0 : Fin 1)))
    (fun i => .var (Fin.natAdd 1 i))

private theorem eval_singletonContextSubst (x : ZFSet.{u})
    (extra : Tuple ZFSet.{u} k) :
    (fun i => (singletonContextSubst k i).eval
      (Fin.addCases (fun _ : Fin 1 => x) extra)) =
      Fin.addCases (fun _ : Fin 1 => ({x, x} : ZFSet.{u})) extra := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    rfl
  · intro j
    simp [singletonContextSubst, PairExpr.eval]

theorem isSimpleSetFunction_singleton :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 1 => ({s 0, s 0} : ZFSet.{u})) := by
  intro k φ
  refine ⟨compilePairSubst (singletonContextSubst k) φ, ?_⟩
  intro args extra
  rw [satisfies_compilePairSubst]
  have hargs : args = (fun _ : Fin 1 => args 0) := by
    funext i
    fin_cases i
    rfl
  rw [hargs, eval_singletonContextSubst]

/-! ## Simultaneous substitutions and genuine term composition -/

/-- A tuple-valued map is simple when it can be eliminated from any context. -/
def IsSimpleTupleMap {n m : Nat}
    (f : Tuple ZFSet.{u} n → Tuple ZFSet.{u} m) : Prop :=
  ∀ k : Nat, ∀ φ : Delta0Formula (m + k),
    ∃ ψ : Delta0Formula (n + k),
      ∀ (args : Tuple ZFSet.{u} n) (extra : Tuple ZFSet.{u} k),
        Satisfies ZFMem ψ (Fin.addCases args extra) ↔
          Satisfies ZFMem φ (Fin.addCases (f args) extra)

/-- Simultaneous simple substitutions compose. -/
theorem IsSimpleTupleMap.comp {l m n : Nat}
    {outer : Tuple ZFSet.{u} m → Tuple ZFSet.{u} l}
    {inner : Tuple ZFSet.{u} n → Tuple ZFSet.{u} m}
    (hOuter : IsSimpleTupleMap outer)
    (hInner : IsSimpleTupleMap inner) :
    IsSimpleTupleMap (fun args => outer (inner args)) := by
  intro k φ
  rcases hOuter k φ with ⟨middle, hmiddle⟩
  rcases hInner k middle with ⟨result, hresult⟩
  refine ⟨result, ?_⟩
  intro args extra
  exact (hresult args extra).trans (hmiddle (inner args) extra)

/-- A simple set function may be precomposed by a simple tuple map. -/
theorem IsSimpleSetFunction.compTuple {m n : Nat}
    {outer : Tuple ZFSet.{u} m → ZFSet.{u}}
    {inner : Tuple ZFSet.{u} n → Tuple ZFSet.{u} m}
    (hOuter : IsSimpleSetFunction outer)
    (hInner : IsSimpleTupleMap inner) :
    IsSimpleSetFunction (fun args => outer (inner args)) := by
  intro k φ
  rcases hOuter k φ with ⟨middle, hmiddle⟩
  rcases hInner k middle with ⟨result, hresult⟩
  refine ⟨result, ?_⟩
  intro args extra
  exact (hresult args extra).trans (hmiddle (inner args) extra)

/-- Extend a coordinate renaming by the untouched extra context. -/
def projectionRename {m n k : Nat} (ρ : Fin m → Fin n) :
    Fin (m + k) → Fin (n + k) :=
  Fin.addCases
    (fun i => Fin.castAdd k (ρ i))
    (fun i => Fin.natAdd n i)

theorem addCases_comp_projectionRename {A : Type u} {m n k : Nat}
    (ρ : Fin m → Fin n) (args : Tuple A n) (extra : Tuple A k) :
    (fun i => Fin.addCases args extra (projectionRename ρ i)) =
      Fin.addCases (fun i => args (ρ i)) extra := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [projectionRename]
  · intro j
    simp [projectionRename]

/-- Every tuple of projections/duplicated variables is a simple tuple map. -/
theorem isSimpleTupleMap_projection {m n : Nat} (ρ : Fin m → Fin n) :
    IsSimpleTupleMap
      (fun args : Tuple ZFSet.{u} n => fun i => args (ρ i)) := by
  intro k φ
  refine ⟨Delta0Formula.rename (projectionRename ρ) φ, ?_⟩
  intro args extra
  rw [Delta0Formula.satisfies_rename,
    addCases_comp_projectionRename]

theorem isSimpleTupleMap_id (n : Nat) :
    IsSimpleTupleMap (fun args : Tuple ZFSet.{u} n => args) := by
  simpa using isSimpleTupleMap_projection (fun i : Fin n => i)

end Constructible.Godel
