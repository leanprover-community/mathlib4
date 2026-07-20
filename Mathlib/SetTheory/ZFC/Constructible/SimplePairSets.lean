/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.SimpleSubstitution

/-!
# Simplicity of ordered pairs and pair sets

This file proves strong simplicity for Kuratowski ordered pairing and for the pair-set operations
used in the Gödel basis.
-/

open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n m k : Nat}

/-! ## Ordered pairing is simple -/

@[expose] public section

/-- Swap coordinates zero and one, leaving all later coordinates fixed. -/
def swapFirstTwo (k : Nat) :
    Fin (1 + (1 + k)) → Fin (1 + (1 + k)) :=
  Fin.addCases
    (fun _ : Fin 1 => Fin.natAdd 1 (Fin.castAdd k (0 : Fin 1)))
    (Fin.addCases
      (fun _ : Fin 1 => Fin.castAdd (1 + k) (0 : Fin 1))
      (fun i : Fin k => Fin.natAdd 1 (Fin.natAdd 1 i)))

/-- Identify the duplicated first input after two simplicity eliminations. -/
def orderedPairDiagonal (k : Nat) : Fin (2 + (1 + k)) → Fin (2 + k) :=
  Fin.addCases
    (fun i : Fin 2 => Fin.castAdd k i)
    (Fin.addCases
      (fun _ : Fin 1 => Fin.castAdd k (0 : Fin 2))
      (fun i : Fin k => Fin.natAdd 2 i))

theorem isSimpleSetFunction_orderedPair :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => ZFSet.pair (s 0) (s 1)) := by
  intro k φ
  rcases isSimpleSetFunction_pair k φ with ⟨pairCtxRaw, hPairCtx⟩
  let arityEq : 2 + k = 1 + (1 + k) := by omega
  let pairCtx : Delta0Formula (1 + (1 + k)) :=
    Delta0Formula.rename (Fin.cast arityEq) pairCtxRaw
  rcases isSimpleSetFunction_singleton (1 + k) pairCtx with
    ⟨singletonCtx, hSingletonCtx⟩
  let swapped : Delta0Formula (1 + (1 + k)) :=
    Delta0Formula.rename (swapFirstTwo k) singletonCtx
  rcases isSimpleSetFunction_pair (1 + k) swapped with
    ⟨diagonalCtx, hDiagonalCtx⟩
  refine ⟨Delta0Formula.rename (orderedPairDiagonal k) diagonalCtx, ?_⟩
  intro args extra
  rw [Delta0Formula.satisfies_rename]
  let x := args 0
  let y := args 1
  let pairArgs : Tuple ZFSet.{u} 2 := ![x, y]
  let singletonArgs : Tuple ZFSet.{u} 1 := ![x]
  let retained : Tuple ZFSet.{u} (1 + k) :=
    Fin.addCases (fun _ : Fin 1 => x) extra
  have hdiagAssign :
      (fun i => Fin.addCases args extra (orderedPairDiagonal k i)) =
        Fin.addCases pairArgs retained := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j <;> rfl
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro q
        fin_cases q
        rfl
      · intro q
        simp [orderedPairDiagonal, retained]
  rw [hdiagAssign, hDiagonalCtx pairArgs retained]
  have hswapAssign :
      (fun i => Fin.addCases (fun _ : Fin 1 => ({x, y} : ZFSet.{u})) retained
          (swapFirstTwo k i)) =
        Fin.addCases singletonArgs
          (Fin.addCases (fun _ : Fin 1 => ({x, y} : ZFSet.{u})) extra) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j
      rfl
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro q
        fin_cases q
        rfl
      · intro q
        simp [swapFirstTwo, retained]
  dsimp only [swapped]
  rw [Delta0Formula.satisfies_rename]
  change
    Satisfies ZFMem singletonCtx
        (fun i => Fin.addCases (fun _ : Fin 1 => ({x, y} : ZFSet.{u}))
          retained (swapFirstTwo k i)) ↔
      Satisfies ZFMem φ
        (Fin.addCases (fun _ : Fin 1 => ZFSet.pair x y) extra)
  rw [hswapAssign]
  rw [hSingletonCtx singletonArgs
    (Fin.addCases (fun _ : Fin 1 => ({x, y} : ZFSet.{u})) extra)]
  dsimp only [pairCtx]
  rw [Delta0Formula.satisfies_rename]
  have hcastAssign :
      (fun i =>
        Fin.addCases (fun _ : Fin 1 => ({x, x} : ZFSet.{u}))
          (Fin.addCases (fun _ : Fin 1 => ({x, y} : ZFSet.{u})) extra)
          (Fin.cast arityEq i)) =
        Fin.addCases
          ![({x, x} : ZFSet.{u}), ({x, y} : ZFSet.{u})] extra := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j <;> rfl
    · intro j
      have hj : Fin.cast arityEq (Fin.natAdd 2 j) =
          Fin.natAdd 1 (Fin.natAdd 1 j) := by
        apply Fin.ext
        simp
        omega
      rw [hj]
      simp
  change
    Satisfies ZFMem pairCtxRaw
        (fun i =>
          Fin.addCases (fun _ : Fin 1 => ({x, x} : ZFSet.{u}))
            (Fin.addCases (fun _ : Fin 1 => ({x, y} : ZFSet.{u})) extra)
            (Fin.cast arityEq i)) ↔
      Satisfies ZFMem φ
        (Fin.addCases (fun _ : Fin 1 => ZFSet.pair x y) extra)
  rw [hcastAssign]
  simpa [singletonArgs, x, y, ZFSet.pair] using
    (hPairCtx ![({x, x} : ZFSet.{u}), ({x, y} : ZFSet.{u})] extra)

/-! ## Eliminating a last-coordinate ordered-pair value -/

/-- Move the last source coordinate to the first target coordinate. -/
def lastToFirst (n : Nat) : Fin (n + 1) → Fin (1 + n) :=
  Fin.lastCases 0 (fun i => Fin.natAdd 1 i)

/-- Put two leading source coordinates after `n` untouched target coordinates. -/
def pairFirstToLast (n : Nat) : Fin (2 + n) → Fin (n + 2) :=
  Fin.addCases
    (fun i : Fin 2 => Fin.cases (Fin.last n).castSucc
      (fun _ => Fin.last (n + 1)) i)
    (fun i : Fin n => i.castSucc.castSucc)

theorem exists_eliminateOrderedPairLast {n : Nat}
    (φ : Delta0Formula (n + 1)) :
    ∃ ψ : Delta0Formula (2 + n),
      ∀ (s : Tuple ZFSet.{u} n) (x y : ZFSet.{u}),
        Satisfies ZFMem ψ (Fin.addCases ![x, y] s) ↔
          Satisfies ZFMem φ (snoc s (ZFSet.pair x y)) := by
  rcases (show IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => ZFSet.pair (s 0) (s 1)) from
    isSimpleSetFunction_orderedPair) n
      (Delta0Formula.rename (lastToFirst n) φ) with ⟨ψ, hψ⟩
  refine ⟨ψ, ?_⟩
  intro s x y
  rw [hψ ![x, y] s, Delta0Formula.satisfies_rename]
  have hassign :
      (fun i =>
        Fin.addCases (fun _ : Fin 1 => ZFSet.pair x y) s
          (lastToFirst n i)) = snoc s (ZFSet.pair x y) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [snoc_last]
      have hlast : lastToFirst n (Fin.last n) = (0 : Fin (1 + n)) := by
        simp [lastToFirst]
      rw [hlast]
      rfl
    · simp [lastToFirst]
  change
    Satisfies ZFMem φ
        (fun i => Fin.addCases (fun _ : Fin 1 => ZFSet.pair x y) s
          (lastToFirst n i)) ↔
      Satisfies ZFMem φ (snoc s (ZFSet.pair x y))
  rw [hassign]

/-- Choose a bounded formula eliminating the final ordered-pair coordinate. -/
noncomputable def eliminateOrderedPairLast {n : Nat}
    (φ : Delta0Formula (n + 1)) : Delta0Formula (2 + n) :=
  Classical.choose (exists_eliminateOrderedPairLast.{u} φ)

@[simp]
theorem satisfies_eliminateOrderedPairLast {n : Nat}
    (φ : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n)
    (x y : ZFSet.{u}) :
    Satisfies ZFMem (eliminateOrderedPairLast.{u} φ)
        (Fin.addCases ![x, y] s) ↔
      Satisfies ZFMem φ (snoc s (ZFSet.pair x y)) :=
  Classical.choose_spec (exists_eliminateOrderedPairLast.{u} φ) s x y

theorem pairFirstToLast_assignment {n : Nat}
    (s : Tuple ZFSet.{u} n) (x y : ZFSet.{u}) :
    (fun i => snoc (snoc s x) y (pairFirstToLast n i)) =
      Fin.addCases ![x, y] s := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.cases ?_ (fun q => ?_) j
    · simp [pairFirstToLast]
    · fin_cases q
      change snoc (snoc s x) y (Fin.last (n + 1)) = y
      simp
  · intro j
    simp [pairFirstToLast]

/-! ## A shared expression compiler for `F₂` and `F₇` -/

/-- The rudimentary operations producing sets of ordered pairs. -/
inductive PairSetKind
  | prod
  | memRel

namespace PairSetKind

/-- The rudimentary-operation index of a pair-set operation. -/
def index : PairSetKind → Fin 9
  | .prod => 2
  | .memRel => 7

/-- Evaluate a pair-set operation. -/
noncomputable def eval (kind : PairSetKind) (x y : ZFSet.{u}) : ZFSet.{u} :=
  op kind.index x y

@[simp]
theorem eval_prod (x y : ZFSet.{u}) :
    eval .prod x y = F2 x y := by rfl

@[simp]
theorem eval_memRel (x y : ZFSet.{u}) :
    eval .memRel x y = F7 x y := by rfl

end PairSetKind

/-- An expression that is a variable or the value of a pair-set operation. -/
inductive PairSetExpr (n : Nat)
  | var (i : Fin n)
  | pairSet (kind : PairSetKind) (left right : Fin n)

namespace PairSetExpr

/-- Evaluate a pair-set expression in an assignment. -/
noncomputable def eval (s : Tuple ZFSet.{u} n) : PairSetExpr n → ZFSet.{u}
  | .var i => s i
  | .pairSet kind i j => kind.eval (s i) (s j)

/-- Rename the variables in a pair-set expression. -/
def rename (ρ : Fin n → Fin m) : PairSetExpr n → PairSetExpr m
  | .var i => .var (ρ i)
  | .pairSet kind i j => .pairSet kind (ρ i) (ρ j)

@[simp]
theorem eval_rename (ρ : Fin n → Fin m) (s : Tuple ZFSet.{u} m)
    (e : PairSetExpr n) :
    eval s (rename ρ e) = eval (fun i => s (ρ i)) e := by
  cases e <;> rfl

end PairSetExpr

/-- `q` belongs to the pair-set selected by `kind`. -/
def memPairSetAt {n : Nat} (kind : PairSetKind)
    (q x y : Fin n) : Delta0Formula n :=
  memOpAt kind.index q x y

@[simp]
theorem satisfies_memPairSetAt {n : Nat} (kind : PairSetKind)
    (q x y : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memPairSetAt kind q x y) s ↔
      s q ∈ kind.eval (s x) (s y) := by
  simp [memPairSetAt, PairSetKind.eval]

/-- Every generated ordered pair lies in coordinate `container`. -/
def generatedPairsSubsetAt {n : Nat} (kind : PairSetKind)
    (container x y : Fin n) : Delta0Formula n :=
  match kind with
  | .prod =>
      .boundedAll x
        (.boundedAll y.castSucc
          (.boundedEx container.castSucc.castSucc
            (kuratowskiPairEqAt (Fin.last (n + 2))
              (Fin.last n).castSucc.castSucc
              (Fin.last (n + 1)).castSucc)))
  | .memRel =>
      .boundedAll x
        (.boundedAll x.castSucc
          (.imp
            (.mem (Fin.last n).castSucc (Fin.last (n + 1)))
            (.boundedEx container.castSucc.castSucc
              (kuratowskiPairEqAt (Fin.last (n + 2))
                (Fin.last n).castSucc.castSucc
                (Fin.last (n + 1)).castSucc))))

@[simp]
theorem satisfies_generatedPairsSubsetAt {n : Nat} (kind : PairSetKind)
    (container x y : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (generatedPairsSubsetAt kind container x y) s ↔
      kind.eval (s x) (s y) ⊆ s container := by
  cases kind with
  | prod =>
      simp only [generatedPairsSubsetAt, Satisfies, satisfies_boundedAll,
        satisfies_kuratowskiPairEqAt, snoc_last, snoc_castSucc,
        PairSetKind.eval_prod]
      constructor
      · intro h q hq
        rcases mem_F2_iff.mp hq with ⟨a, ha, b, hb, rfl⟩
        rcases h a ha b hb with ⟨p, hp, hpEq⟩
        simpa [hpEq] using hp
      · intro h a ha b hb
        refine ⟨ZFSet.pair a b, h ?_, rfl⟩
        exact mem_F2_iff.mpr ⟨a, ha, b, hb, rfl⟩
  | memRel =>
      simp only [generatedPairsSubsetAt, Satisfies, satisfies_boundedAll,
        satisfies_imp, satisfies_kuratowskiPairEqAt, snoc_last,
        snoc_castSucc, PairSetKind.eval_memRel]
      constructor
      · intro h q hq
        rcases mem_F7_iff.mp hq with ⟨a, ha, b, hb, rfl, hab⟩
        rcases h a ha b hb hab with ⟨p, hp, hpEq⟩
        simpa [hpEq] using hp
      · intro h a ha b hb hab
        refine ⟨ZFSet.pair a b, h ?_, rfl⟩
        exact mem_F7_iff.mpr ⟨a, ha, b, hb, rfl, hab⟩

/-- Extensional equality between a variable and a pair-set. -/
def eqVarPairSetAt {n : Nat} (a : Fin n) (kind : PairSetKind)
    (x y : Fin n) : Delta0Formula n :=
  .conj
    (.boundedAll a
      (memPairSetAt kind (Fin.last n) x.castSucc y.castSucc))
    (generatedPairsSubsetAt kind a x y)

@[simp]
theorem satisfies_eqVarPairSetAt {n : Nat} (a : Fin n)
    (kind : PairSetKind) (x y : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqVarPairSetAt a kind x y) s ↔
      s a = kind.eval (s x) (s y) := by
  simp only [eqVarPairSetAt, Satisfies, satisfies_boundedAll,
    satisfies_memPairSetAt, satisfies_generatedPairsSubsetAt, snoc_last,
    snoc_castSucc]
  constructor
  · rintro ⟨hsub, hsup⟩
    exact le_antisymm hsub hsup
  · intro h
    exact ⟨fun q hq => h ▸ hq, fun q hq => h ▸ hq⟩

/-- A bounded contradiction using the given coordinate. -/
def falseAt {n : Nat} (i : Fin n) : Delta0Formula n :=
  .neg (.eq i i)

/-- Compile membership between compatible pair-set expressions. -/
def memPairSetExpr {n : Nat} :
    PairSetExpr n → PairSetExpr n → Delta0Formula n
  | .var a, .var b => .mem a b
  | .var a, .pairSet kind x y => memPairSetAt kind a x y
  | .pairSet kind x y, .var a =>
      .boundedEx a
        (eqVarPairSetAt (Fin.last n) kind x.castSucc y.castSucc)
  | .pairSet _ x _, .pairSet _ _ _ => falseAt x

/-- Compile equality between compatible pair-set expressions. -/
def eqPairSetExpr {n : Nat} :
    PairSetExpr n → PairSetExpr n → Delta0Formula n
  | .var a, .var b => .eq a b
  | .var a, .pairSet kind x y => eqVarPairSetAt a kind x y
  | .pairSet kind x y, .var a => eqVarPairSetAt a kind x y
  | .pairSet _ x _, .pairSet _ _ _ => .eq x x

/-- Two substituted expressions are compatible when any two structured
outputs denote the very same pair-set.  The actual context substitution has
exactly one structured output, and lifting under binders preserves this
invariant. -/
def PairSetExpr.Compatible {n : Nat} :
    PairSetExpr n → PairSetExpr n → Prop
  | .pairSet kind x y, .pairSet kind' x' y' =>
      kind = kind' ∧ x = x' ∧ y = y'
  | _, _ => True

@[simp]
theorem satisfies_memPairSetExpr {n : Nat} (left right : PairSetExpr n)
    (hcompat : left.Compatible right) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memPairSetExpr left right) s ↔
      left.eval s ∈ right.eval s := by
  cases left <;> cases right
  · change Satisfies ZFMem (.mem _ _) s ↔ _
    simp [Satisfies, PairSetExpr.eval]
  · change Satisfies ZFMem (memPairSetAt _ _ _ _) s ↔ _
    simp [satisfies_memPairSetAt, PairSetExpr.eval]
  · change Satisfies ZFMem
      (.boundedEx _ (eqVarPairSetAt _ _ _ _)) s ↔ _
    simp [Satisfies, PairSetExpr.eval]
  · rcases hcompat with ⟨rfl, rfl, rfl⟩
    change Satisfies ZFMem (falseAt _) s ↔ _
    simp [falseAt, Satisfies, PairSetExpr.eval, ZFSet.mem_irrefl]

@[simp]
theorem satisfies_eqPairSetExpr {n : Nat} (left right : PairSetExpr n)
    (hcompat : left.Compatible right) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqPairSetExpr left right) s ↔
      left.eval s = right.eval s := by
  cases left <;> cases right
  · change Satisfies ZFMem (.eq _ _) s ↔ _
    simp [Satisfies, PairSetExpr.eval]
  · change Satisfies ZFMem (eqVarPairSetAt _ _ _ _) s ↔ _
    simp [PairSetExpr.eval]
  · change Satisfies ZFMem (eqVarPairSetAt _ _ _ _) s ↔ _
    rw [satisfies_eqVarPairSetAt]
    exact eq_comm
  · rcases hcompat with ⟨rfl, rfl, rfl⟩
    change Satisfies ZFMem (.eq _ _) s ↔ _
    simp [Satisfies, PairSetExpr.eval]

/-- Every structured expression in a simultaneous substitution is the same
distinguished output. -/
def PairSetSubstCompatible {m n : Nat}
    (σ : Fin m → PairSetExpr n) : Prop :=
  ∀ i j, (σ i).Compatible (σ j)

theorem PairSetExpr.compatible_rename {n m : Nat}
    {left right : PairSetExpr n} (ρ : Fin n → Fin m)
    (h : left.Compatible right) :
    (left.rename ρ).Compatible (right.rename ρ) := by
  cases left <;> cases right
  · exact True.intro
  · exact True.intro
  · exact True.intro
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩

/-- Lift a compatible substitution through a newly bound last variable. -/
def liftPairSetSubst {m n : Nat} (σ : Fin m → PairSetExpr n) :
    Fin (m + 1) → PairSetExpr (n + 1) :=
  Fin.lastCases (.var (Fin.last n))
    (fun i => (σ i).rename Fin.castSucc)

theorem eval_liftPairSetSubst {m n : Nat}
    (σ : Fin m → PairSetExpr n) (s : Tuple ZFSet.{u} n)
    (z : ZFSet.{u}) :
    (fun i => (liftPairSetSubst σ i).eval (snoc s z)) =
      snoc (fun i => (σ i).eval s) z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [liftPairSetSubst, PairSetExpr.eval]
  · cases h : σ j <;>
      simp [liftPairSetSubst, PairSetExpr.eval, PairSetExpr.rename, h]

theorem pairSetSubstCompatible_lift {m n : Nat}
    {σ : Fin m → PairSetExpr n} (hσ : PairSetSubstCompatible σ) :
    PairSetSubstCompatible (liftPairSetSubst σ) := by
  intro i j
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [liftPairSetSubst, PairSetExpr.Compatible]
  · refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [liftPairSetSubst, PairSetExpr.Compatible]
    · simpa [liftPairSetSubst] using
        (PairSetExpr.compatible_rename Fin.castSucc (hσ i' j'))

/-- Compile a compatible substitution by variables and one F2/F7 output. -/
noncomputable def compilePairSetSubst {m n : Nat}
    (σ : Fin m → PairSetExpr n) : Delta0Formula m → Delta0Formula n
  | .mem i j => memPairSetExpr (σ i) (σ j)
  | .eq i j => eqPairSetExpr (σ i) (σ j)
  | .neg φ => .neg (compilePairSetSubst σ φ)
  | .conj φ ψ =>
      .conj (compilePairSetSubst σ φ) (compilePairSetSubst σ ψ)
  | .boundedEx i φ =>
      match σ i with
      | .var bound =>
          .boundedEx bound
            (compilePairSetSubst (liftPairSetSubst σ) φ)
      | .pairSet kind left right =>
          let body := compilePairSetSubst (liftPairSetSubst σ) φ
          let pairBody := Delta0Formula.rename (pairFirstToLast n)
            (eliminateOrderedPairLast.{u} body)
          match kind with
          | .prod =>
              .boundedEx left (.boundedEx right.castSucc pairBody)
          | .memRel =>
              .boundedEx left (.boundedEx left.castSucc
                (.conj
                  (.mem (Fin.last n).castSucc (Fin.last (n + 1)))
                  pairBody))

@[simp]
theorem satisfies_pairBody {m n : Nat}
    (σ : Fin m → PairSetExpr n) (φ : Delta0Formula (m + 1))
    (s : Tuple ZFSet.{u} n) (x y : ZFSet.{u})
    (ih : ∀ (s' : Tuple ZFSet.{u} (n + 1)),
      Satisfies ZFMem
          (compilePairSetSubst.{u} (liftPairSetSubst σ) φ) s' ↔
        Satisfies ZFMem φ
          (fun i => (liftPairSetSubst σ i).eval s')) :
    Satisfies ZFMem
        (Delta0Formula.rename (pairFirstToLast n)
          (eliminateOrderedPairLast.{u}
            (compilePairSetSubst.{u} (liftPairSetSubst σ) φ)))
        (snoc (snoc s x) y) ↔
      Satisfies ZFMem φ
        (snoc (fun i => (σ i).eval s) (ZFSet.pair x y)) := by
  rw [Delta0Formula.satisfies_rename,
    pairFirstToLast_assignment]
  calc
    Satisfies ZFMem
        (eliminateOrderedPairLast.{u}
          (compilePairSetSubst.{u} (liftPairSetSubst σ) φ))
        (Fin.addCases ![x, y] s) ↔
      Satisfies ZFMem
        (compilePairSetSubst.{u} (liftPairSetSubst σ) φ)
        (snoc s (ZFSet.pair x y)) :=
      satisfies_eliminateOrderedPairLast.{u}
        (compilePairSetSubst.{u} (liftPairSetSubst σ) φ) s x y
    _ ↔ Satisfies ZFMem φ
        (fun i => (liftPairSetSubst σ i).eval
          (snoc s (ZFSet.pair x y))) :=
      ih (snoc s (ZFSet.pair x y))
    _ ↔ Satisfies ZFMem φ
        (snoc (fun i => (σ i).eval s) (ZFSet.pair x y)) := by
      rw [eval_liftPairSetSubst]

/-- The substitution placing one pair-set value before the remaining context. -/
def pairSetContextSubst (kind : PairSetKind) (k : Nat) :
    Fin (1 + k) → PairSetExpr (2 + k) :=
  Fin.addCases
    (fun _ => .pairSet kind
      (Fin.castAdd k (0 : Fin 2)) (Fin.castAdd k (1 : Fin 2)))
    (fun i => .var (Fin.natAdd 2 i))

theorem pairSetContextSubst_compatible (kind : PairSetKind) (k : Nat) :
    PairSetSubstCompatible (pairSetContextSubst kind k) := by
  intro i j
  refine Fin.addCases ?_ ?_ i
  · intro a
    fin_cases a
    refine Fin.addCases ?_ ?_ j
    · intro b
      fin_cases b
      simp [pairSetContextSubst, PairSetExpr.Compatible]
    · intro b
      simp [pairSetContextSubst, PairSetExpr.Compatible]
  · intro a
    refine Fin.addCases ?_ ?_ j
    · intro b
      simp [pairSetContextSubst, PairSetExpr.Compatible]
    · intro b
      simp [pairSetContextSubst, PairSetExpr.Compatible]

theorem eval_pairSetContextSubst (kind : PairSetKind)
    (x y : ZFSet.{u}) (extra : Tuple ZFSet.{u} k) :
    (fun i => (pairSetContextSubst kind k i).eval
      (Fin.addCases ![x, y] extra)) =
      Fin.addCases (fun _ : Fin 1 => kind.eval x y) extra := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    rfl
  · intro j
    simp [pairSetContextSubst, PairSetExpr.eval]

@[simp]
theorem satisfies_compilePairSetSubst {m n : Nat}
    (σ : Fin m → PairSetExpr n) (hσ : PairSetSubstCompatible σ)
    (φ : Delta0Formula m) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (compilePairSetSubst.{u} σ φ) s ↔
      Satisfies ZFMem φ (fun i => (σ i).eval s) := by
  induction φ generalizing n with
  | mem i j =>
      simpa [compilePairSetSubst] using
        (satisfies_memPairSetExpr (σ i) (σ j) (hσ i j) s)
  | eq i j =>
      simpa [compilePairSetSubst] using
        (satisfies_eqPairSetExpr (σ i) (σ j) (hσ i j) s)
  | neg φ ih =>
      simp [compilePairSetSubst, ih σ hσ]
  | conj φ ψ ihφ ihψ =>
      simp [compilePairSetSubst, ihφ σ hσ, ihψ σ hσ]
  | boundedEx i φ ih =>
      cases hbound : σ i with
      | var bound =>
          simp only [compilePairSetSubst, hbound, Satisfies]
          constructor
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [PairSetExpr.eval, hbound] using hz
            · rw [ih (liftPairSetSubst σ)
                (pairSetSubstCompatible_lift hσ)] at hφ
              simpa only [eval_liftPairSetSubst] using hφ
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [PairSetExpr.eval, hbound] using hz
            · rw [ih (liftPairSetSubst σ)
                (pairSetSubstCompatible_lift hσ)]
              simpa only [eval_liftPairSetSubst] using hφ
      | pairSet kind left right =>
          have hpair (x y : ZFSet.{u}) :
              Satisfies ZFMem
                  (Delta0Formula.rename (pairFirstToLast n)
                    (eliminateOrderedPairLast.{u}
                      (compilePairSetSubst.{u}
                        (liftPairSetSubst σ) φ)))
                  (snoc (snoc s x) y) ↔
                Satisfies ZFMem φ
                  (snoc (fun j => (σ j).eval s)
                    (ZFSet.pair x y)) :=
            satisfies_pairBody σ φ s x y
              (fun s' => ih (liftPairSetSubst σ)
                (pairSetSubstCompatible_lift hσ) s')
          cases kind with
          | prod =>
              simp only [compilePairSetSubst, hbound, Satisfies,
                snoc_castSucc, PairSetExpr.eval, PairSetKind.eval_prod]
              constructor
              · rintro ⟨x, hx, y, hy, hbody⟩
                refine ⟨ZFSet.pair x y, ?_, ?_⟩
                · exact mem_F2_iff.mpr ⟨x, hx, y, hy, rfl⟩
                · exact (hpair x y).mp hbody
              · rintro ⟨q, hq, hbody⟩
                rcases mem_F2_iff.mp hq with ⟨x, hx, y, hy, rfl⟩
                exact ⟨x, hx, y, hy, (hpair x y).mpr hbody⟩
          | memRel =>
              simp only [compilePairSetSubst, hbound, Satisfies,
                snoc_castSucc, snoc_last, PairSetExpr.eval,
                PairSetKind.eval_memRel]
              constructor
              · rintro ⟨x, hx, y, hy, hxy, hbody⟩
                refine ⟨ZFSet.pair x y, ?_, ?_⟩
                · exact mem_F7_iff.mpr ⟨x, hx, y, hy, rfl, hxy⟩
                · exact (hpair x y).mp hbody
              · rintro ⟨q, hq, hbody⟩
                rcases mem_F7_iff.mp hq with
                  ⟨x, hx, y, hy, rfl, hxy⟩
                exact ⟨x, hx, y, hy, hxy, (hpair x y).mpr hbody⟩

theorem isSimpleSetFunction_pairSet (kind : PairSetKind) :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => kind.eval (s 0) (s 1)) := by
  intro k φ
  refine ⟨compilePairSetSubst.{u} (pairSetContextSubst kind k) φ, ?_⟩
  intro args extra
  rw [satisfies_compilePairSetSubst _
    (pairSetContextSubst_compatible kind k)]
  have hargs : args = ![args 0, args 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hargs, eval_pairSetContextSubst]
  simp

theorem isSimpleSetFunction_F2 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F2 (s 0) (s 1)) := by
  simpa using isSimpleSetFunction_pairSet.{u} .prod

theorem isSimpleSetFunction_F7 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F7 (s 0) (s 1)) := by
  simpa using isSimpleSetFunction_pairSet.{u} .memRel

end

end Constructible.Godel
