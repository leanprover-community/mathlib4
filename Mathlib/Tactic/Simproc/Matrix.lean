/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Data.Matrix.Reflection

/-!
# Simprocs for matrices

In this file we provide a simproc and a "rw proc" for transpose of explicit matrices.

Existing theorems are `Matrix.cons_transpose` and a simproc `Matrix.cons_val`, but this simproc
and rw proc aim to do it in one step to optimise the proof term and intermediate goal sizes.
-/

open Matrix
open Lean Meta Simp Simproc Tactic Qq

attribute [-simp] cons_transpose

namespace Qq

/-- Decompose a vector expression into a vector of expressions. -/
def piFinLit? {u : Level} {n : ℕ} {R : Q(Type u)} (e : Q(Fin $n → $R)) :
    MetaM (Option (Fin n → Q($R))) := do
  match n with
  | 0 =>
    let ~q(![]) := e | return .none
    return .some ![]
  | _+1 =>
    let ~q(vecCons $h $et) := e | return .none
    let .some t ← piFinLit? et | return .none
    return .some (vecCons h t)

/-- Decompose a "double vector" expression, i.e. `Fin m → Fin n → R`, into a double vector of
expressions. -/
def piFinPiFinLit? {u : Level} {m n : ℕ} {R : Q(Type u)} (e : Q(Fin $m → Fin $n → $R)) :
    MetaM (Option (Fin m → Fin n → Q($R))) := do
  match m with
  | 0 =>
    let ~q(![]) := e | return .none
    return .some ![]
  | _+1 =>
    let ~q(vecCons $h $et) := e | return .none
    let .some h ← piFinLit? h | return .none
    let .some t ← piFinPiFinLit? et | return .none
    return .some (vecCons h t)

/-- Decompose a matrix expression into a matrix of expressions. -/
def matrixLit? {u : Level} {m n : ℕ} {R : Q(Type u)} (eM : Q(Matrix (Fin $m) (Fin $n) $R)) :
    MetaM (Option (Matrix (Fin m) (Fin n) Q($R))) := do
  let ~q(of $eM) := eM | return .none
  let .some M ← piFinPiFinLit? eM | return .none
  return of M

/-- Given a matrix of expressions, construct a proof of `(mkLiteralQ M)ᵀ = mkLiteralQ (Mᵀ)`. -/
def mkTransposeProof {u : Level} {α : Q(Type u)} {m n : ℕ} (M : Matrix (Fin m) (Fin n) Q($α)) :
    (P : Q(Prop)) × Q($P) :=
  ⟨q($(mkLiteralQ M)ᵀ = $(mkLiteralQ Mᵀ)),
  cast (by rfl) q((etaExpand_eq $(mkLiteralQ M)ᵀ).symm)⟩

/-- Prove a statement of the form
```
theorem Matrix.transpose₂₃ {α : Type*} (a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ : α) :
    !![a₀₀, a₀₁, a₀₂; a₁₀, a₁₁, a₁₂]ᵀ = !![a₀₀, a₁₀; a₀₁, a₁₁; a₀₂, a₁₂] :=
  (etaExpand_eq _).symm
```
Returns the type of this statement and its proof. -/
def mkTransposeProp (u : Level) (m n : ℕ) : (P : Q(Prop)) × Q($P) :=
  let α : Q(Type u) := Expr.fvar ⟨`α⟩
  let varName (i : Fin m) (j : Fin n) : Name :=
    ("a_" ++ i.val.repr ++ "_" ++ j.val.repr).toName
  let var (i : Fin m) (j : Fin n) : Q($α) :=
    .fvar ⟨varName i j⟩
  let ⟨P', pf'⟩ := mkTransposeProof (of var)
  let argsE : List Expr :=
    [α] ++ (List.finRange m).flatMap fun i : Fin m ↦ List.ofFn fun j : Fin n ↦ by exact var i j
  let argsD : List LocalDecl :=
    [.cdecl 0 ⟨`α⟩ `α (.sort u.succ) .implicit .default] ++
    (List.finRange m).flatMap fun i : Fin m ↦ List.ofFn fun j : Fin n ↦
      .cdecl (finProdFinEquiv (i, j) + 1) ⟨varName i j⟩ (varName i j) α .default .default
  ⟨Closure.mkForall argsD.toArray (P'.abstract argsE.toArray),
  Closure.mkLambda argsD.toArray (pf'.abstract argsE.toArray)⟩

end Qq

open Elab Tactic

/-- A custom theorem for reducing transpose of explicit matrices. For example, `transpose_of% 2 3`
is the theorem saying `!![a, b, c; d, e, f]ᵀ = !![a, d; b, e; c, f]`. Usage:

```lean
example : (!![1, 2, 3; 4, 5, 6]ᵀ : Matrix (Fin (2+1)) (Fin 2) ℤ) = !![1, 4; 2, 5; 3, 6] := by
  rw [transpose_of% 2 3]
``` -/
elab:max (name := transpose_tac_elab)
    "transpose_of% " mStx:term:max nStx:term:max : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  let m : Q(Nat) ← Term.elabTermEnsuringType mStx (mkConst ``Nat)
  let n : Q(Nat) ← Term.elabTermEnsuringType nStx (mkConst ``Nat)
  let some m ← (evalNat m).run
    | throwErrorAt mStx "Expecting a natural number, have{indentD m}"
  let some n ← (evalNat n).run
    | throwErrorAt nStx "Expecting a natural number, have{indentD n}"
  let ⟨P, h⟩ := mkTransposeProp u m n
  let .some h ← checkTypeQ h P | throwError m!"Wrong proof generated for {m}, {n}."
  mkExpectedTypeHint h P

example (u : Matrix (Fin 2) (Fin 3) ℤ) (v : Matrix (Fin 3) (Fin 2) ℤ)
    (hu : u = !![1, 2, 3; 4, 5, 6]) (hv : v = !![1, 4; 2, 5; 3, 6]) :
    uᵀ = v := by
  rw [hu, transpose_of% 2 3, hv]

-- Here we use the convention that `e{name}` is the expression for `{name}`, e.g. `eMT` is the
-- expression corresponding to the transpose of the matrix `M`.
/-- A simproc for terms of the form `Matrix.transpose (Matrix.of _)`. Usage:

```lean
example : (!![1, 2, 3; 4, 5, 6]ᵀ : Matrix (Fin (2+1)) (Fin 2) ℤ) = !![1, 4; 2, 5; 3, 6] := by
  simp
```
-/
simproc matrix_transpose (Matrix.transpose (Matrix.of _)) := .ofQ fun u α eMT ↦ do
  let .succ _ := u | return .continue
  let ~q(@Matrix (Fin (OfNat.ofNat $en)) (Fin (OfNat.ofNat $em)) $R) := α | return .continue
  let ~q(transpose $eM) := eMT | return .continue
  let .some M ← matrixLit? (m := em.natLit!) (n := en.natLit!) (R := R) eM | return .continue
  let ⟨P, h⟩ := mkTransposeProof M
  let ~q($lhs = $rhs) := P | return .continue
  return .visit { expr := rhs, proof? := .some h }

example (u : Matrix (Fin 2) (Fin 3) ℤ) (v : Matrix (Fin 3) (Fin 2) ℤ)
    (hu : u = !![1, 2, 3; 4, 5, 6]) (hv : v = !![1, 4; 2, 5; 3, 6]) :
    uᵀ = v := by
  rw [hu]
  simp only [matrix_transpose]
  rw [hv]



local elab "transpose_tac" : tactic => do
  Lean.Elab.Tactic.liftMetaFinishingTactic fun m => do
    trace[debug] m!"{m}"
    trace[debug] m!"{(← inferTypeQ (Expr.mvar m)).2.1}"
    let ⟨0, ~q((of (vecCons $head $tail))ᵀ = $rhs), h⟩ := ← inferTypeQ (Expr.mvar m)
      | throwError "Could not infer type for eta"
    trace[debug] m!"{head}, {tail}"
    -- have h := .mvar m
    return ()
  --   let .some n := en.nat?
  --     | throwError "Vector is not of a known length"
  --   have new_rhs : Q(Fin $en → $α) := PiFin.mkLiteralQ fun i : Fin n =>
  --     let ei : Q(Fin $en) := Lean.toExpr i
  --     q($lhs $ei)
  --   have : $new_rhs =Q etaExpand $lhs := ⟨⟩
  --   Lean.commitIfNoEx do
  --     let .defEq _ := ← isDefEqQ q($rhs) q($new_rhs)
  --       | throwError "Could not assign RHS"
  --     h.mvarId!.assignIfDefEq q(etaExpand_eq $lhs |>.symm)

set_option trace.debug true

/-- This "rw_proc" computes the transpose of an explicit matrix such as `!![a, b, c; d, e, f]`. -/
theorem transpose_eta {m n α} (head : Fin n → α) (tail : Fin m → Fin n → α)
      {rhs : Matrix (Fin n) (Fin (m + 1)) α}
      (pf : (of (vecCons head tail))ᵀ = rhs := by transpose_tac) :
    (of (vecCons head tail))ᵀ = rhs := pf

example (u : Matrix (Fin 2) (Fin 3) ℤ) (v : Matrix (Fin 3) (Fin 2) ℤ)
    (hu : u = !![1, 2, 3; 4, 5, 6]) (hv : v = !![1, 4; 2, 5; 3, 6]) :
    uᵀ = v := by
  rw [hu, transpose_eta, hv]

namespace Aaron

@[specialize]
private def uVec (nam : Nat → Nat → FVarId) {u : Level} (α : Q(Type u))
    (n m k : Nat) (ih : Expr) : Expr :=
  match m with
  | 0 => ih
  | m + 1 =>
    have bb : Q($α) := .fvar (nam n m)
    have ih : Q(Fin $k → $α) := ih
    have next : Q(Fin ($k + 1) → $α) := q(Matrix.vecCons $bb $ih)
    uVec nam α n m (k + 1) next

@[specialize]
private def uMatrix (nam : Nat → Nat → FVarId) {u : Level} (α : Q(Type u))
    (n m k : Nat) (ih : Expr) : Expr :=
  match n with
  | 0 => ih
  | n + 1 =>
    have bb : Q(Fin $m → $α) := uVec nam α n m 0 (show Q(Fin 0 → $α) from q(Matrix.vecEmpty))
    have ih : Q(Fin $k → Fin $m → $α) := ih
    have next : Q(Fin ($k + 1) → Fin $m → $α) := q(Matrix.vecCons $bb $ih)
    uMatrix nam α n m (k + 1) next

private def coabst (α ih : Expr) (m t : Nat) : Expr :=
  match t with
  | 0 => ih
  | t + 1 =>
    have nam : String := s!"r{t/m}c{t%m}"
    coabst α (.lam (.str .anonymous nam) α ih .default) m t

def mkTransposeTheorem (u : Level) (n m : Nat) : Expr :=
  have α : Q(Type u) := .fvar ⟨`α⟩
  have nam (n m : Nat) : FVarId := ⟨.num (.num .anonymous n) m⟩
  have array : Array Expr := Id.run do
    let mut arr : Array Expr := Array.emptyWithCapacity (n * m)
    for i in [:n] do
      for j in [:m] do
        arr := arr.push (.fvar ⟨.num (.num .anonymous i) j⟩)
    return arr
  have uM : Q(Fin $n → Fin $m → $α) :=
    uMatrix nam α n m 0 (show Q(Fin 0 → Fin $m → $α) from q(Matrix.vecEmpty))
  have vM : Q(Fin $m → Fin $n → $α) :=
    uMatrix (fun n m => nam m n) α m n 0 (show Q(Fin 0 → Fin $n → $α) from q(Matrix.vecEmpty))
  have lhs : Q(Matrix (Fin $m) (Fin $n) $α) := q(.transpose (.of $uM))
  have rhs : Q(Matrix (Fin $m) (Fin $n) $α) := q(.of $vM)
  have eqPrf : Q($lhs = ($lhs).etaExpand) := q(($lhs).etaExpand_eq.symm)
  have eqExpr : Q(Prop) := q($lhs = $rhs)
  have pe : Expr := .abstract (.app (.app (.const ``id [levelZero]) eqExpr) eqPrf) array
  have ek : Expr := .lam (.str .anonymous "α") (.sort u.succ)
    ((coabst α pe m (n * m)).abstract #[α]) .implicit
  ek

end Aaron


namespace Aaron2

@[specialize]
private def uVec {u : Level} {α : Q(Type u)} (nam : Nat → Nat → Q($α))
    (n m k : Nat) (ih : Q(Fin $k → $α)) : Q(Fin $m → $α) := -- k ≤ m
  match m with
  | 0 => ih
  | m + 1 => uVec nam n m (k + 1) q(vecCons $(nam n m) $ih)

@[specialize]
private def uVecVec {u : Level} {α : Q(Type u)} (nam : Nat → Nat → Q($α))
    (n m k : Nat) (ih : Q(Fin $k → Fin $m → $α)) : Q(Fin $n → Fin $m → $α) := -- k ≤ n
  match n with
  | 0 => ih
  | n + 1 =>
    have bb : Q(Fin $m → $α) := uVec nam n m 0 q(![])
    uVecVec nam n m (k + 1) q(vecCons $bb $ih)

/-- Converts `f #0 #1 #2` to `fun a₀ a₁ a₂ ↦ f a₀ a₁ a₂`.

This assumes they are all explicit variables with the same type. -/
def mkLambdas (names : Array Name) (type : Expr) (b : Expr) : Expr :=
  names.foldr (fun n b' ↦ .lam n type b' .default) b

def mkTransposeTheorem (u : Level) (n m : Nat) : Q(Prop) :=
  have α : Q(Type u) := .fvar ⟨.anonymous⟩
  have nam (i j : Nat) : Q($α) := .fvar ⟨.num (.num .anonymous i) j⟩
  have uM : Q(Matrix (Fin $n) (Fin $m) $α) := q(of $(uVecVec nam n m 0 q(![])))
  have lhs : Q(Matrix (Fin $m) (Fin $n) $α) := q($uMᵀ)
  have rhs : Q(Matrix (Fin $m) (Fin $n) $α) := q(of $(uVecVec (flip nam) m n 0 q(![])))
  have eqProp : Q(Prop) := q($lhs = $rhs)
  have eqPrf' : Q($lhs = ($lhs).etaExpand) := q(($lhs).etaExpand_eq.symm)
  have eqPrf : Q($lhs = $rhs) := mkApp2 (.const ``id [.zero]) eqProp eqPrf'
  --have equiv : Fin (n * m) ≃ Fin n × Fin m := finProdFinEquiv.symm
  have names : Array Name := .ofFn fun t : Fin (n * m) ↦ s!"r{t/m}c{t%m}".toName
  have args : Array Q($α) := .ofFn fun t : Fin (n * m) ↦ nam (t/m) (t%m)
  have lam_eqPrf : Q(Prop) := mkLambdas names q($α) (eqPrf.abstract args)
  .lam `α q(Type u) (lam_eqPrf.abstract #[α]) .implicit

end Aaron2


open Meta Elab in
elab:max (name := transpose_tac_elab_aaron) "transpose_of_aaron% " mStx:num nStx:num : term => do
  let u ← mkFreshLevelMVar
  return Aaron.mkTransposeTheorem u mStx.getNat nStx.getNat

open Meta Elab in
elab:max (name := transpose_tac_elab_aaron2) "transpose_of_aaron2% " mStx:num nStx:num : term => do
  let u ← mkFreshLevelMVar
  return Aaron2.mkTransposeTheorem u mStx.getNat nStx.getNat

#check transpose_of_aaron% 2 3
#check transpose_of_aaron2% 2 3

namespace Test

def M : ℕ := 23
def N : ℕ := 21

/-  #eval of fun (i : Fin M) (j : Fin N) ↦ finProdFinEquiv (i, j)
 #eval of fun (i : Fin N) (j : Fin M) ↦ finProdFinEquiv (j, i) -/

def U : Matrix (Fin 23) (Fin 21) ℕ :=
!![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20;
  21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41;
  42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62;
  63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83;
  84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104;
  105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125;
  126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146;
  147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167;
  168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188;
  189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209;
  210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230;
  231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251;
  252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272;
  273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293;
  294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314;
  315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335;
  336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356;
  357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377;
  378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398;
  399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419;
  420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440;
  441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461;
  462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482]

def V : Matrix (Fin 21) (Fin 23) ℕ :=
!![0, 21, 42, 63, 84, 105, 126, 147, 168, 189, 210, 231, 252, 273, 294, 315, 336, 357, 378, 399, 420, 441, 462;
  1, 22, 43, 64, 85, 106, 127, 148, 169, 190, 211, 232, 253, 274, 295, 316, 337, 358, 379, 400, 421, 442, 463;
  2, 23, 44, 65, 86, 107, 128, 149, 170, 191, 212, 233, 254, 275, 296, 317, 338, 359, 380, 401, 422, 443, 464;
  3, 24, 45, 66, 87, 108, 129, 150, 171, 192, 213, 234, 255, 276, 297, 318, 339, 360, 381, 402, 423, 444, 465;
  4, 25, 46, 67, 88, 109, 130, 151, 172, 193, 214, 235, 256, 277, 298, 319, 340, 361, 382, 403, 424, 445, 466;
  5, 26, 47, 68, 89, 110, 131, 152, 173, 194, 215, 236, 257, 278, 299, 320, 341, 362, 383, 404, 425, 446, 467;
  6, 27, 48, 69, 90, 111, 132, 153, 174, 195, 216, 237, 258, 279, 300, 321, 342, 363, 384, 405, 426, 447, 468;
  7, 28, 49, 70, 91, 112, 133, 154, 175, 196, 217, 238, 259, 280, 301, 322, 343, 364, 385, 406, 427, 448, 469;
  8, 29, 50, 71, 92, 113, 134, 155, 176, 197, 218, 239, 260, 281, 302, 323, 344, 365, 386, 407, 428, 449, 470;
  9, 30, 51, 72, 93, 114, 135, 156, 177, 198, 219, 240, 261, 282, 303, 324, 345, 366, 387, 408, 429, 450, 471;
  10, 31, 52, 73, 94, 115, 136, 157, 178, 199, 220, 241, 262, 283, 304, 325, 346, 367, 388, 409, 430, 451, 472;
  11, 32, 53, 74, 95, 116, 137, 158, 179, 200, 221, 242, 263, 284, 305, 326, 347, 368, 389, 410, 431, 452, 473;
  12, 33, 54, 75, 96, 117, 138, 159, 180, 201, 222, 243, 264, 285, 306, 327, 348, 369, 390, 411, 432, 453, 474;
  13, 34, 55, 76, 97, 118, 139, 160, 181, 202, 223, 244, 265, 286, 307, 328, 349, 370, 391, 412, 433, 454, 475;
  14, 35, 56, 77, 98, 119, 140, 161, 182, 203, 224, 245, 266, 287, 308, 329, 350, 371, 392, 413, 434, 455, 476;
  15, 36, 57, 78, 99, 120, 141, 162, 183, 204, 225, 246, 267, 288, 309, 330, 351, 372, 393, 414, 435, 456, 477;
  16, 37, 58, 79, 100, 121, 142, 163, 184, 205, 226, 247, 268, 289, 310, 331, 352, 373, 394, 415, 436, 457, 478;
  17, 38, 59, 80, 101, 122, 143, 164, 185, 206, 227, 248, 269, 290, 311, 332, 353, 374, 395, 416, 437, 458, 479;
  18, 39, 60, 81, 102, 123, 144, 165, 186, 207, 228, 249, 270, 291, 312, 333, 354, 375, 396, 417, 438, 459, 480;
  19, 40, 61, 82, 103, 124, 145, 166, 187, 208, 229, 250, 271, 292, 313, 334, 355, 376, 397, 418, 439, 460, 481;
  20, 41, 62, 83, 104, 125, 146, 167, 188, 209, 230, 251, 272, 293, 314, 335, 356, 377, 398, 419, 440, 461, 482]

set_option trace.profiler true

theorem test1 : Uᵀ = V := by
  rw [U, transpose_of_aaron% 23 21, V]

theorem test2 : Uᵀ = V := by
  rw [U, transpose_of_aaron2% 23 21, V]

end Test
