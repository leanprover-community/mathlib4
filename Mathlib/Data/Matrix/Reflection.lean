/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Tuple.Reflection

#align_import data.matrix.reflection from "leanprover-community/mathlib"@"820b22968a2bc4a47ce5cf1d2f36a9ebe52510aa"

/-!
# Lemmas for concrete matrices `Matrix (Fin m) (Fin n) α`

This file contains alternative definitions of common operators on matrices that expand
definitionally to the expected expression when evaluated on `!![]` notation.

This allows "proof by reflection", where we prove `A = !![A 0 0, A 0 1;  A 1 0, A 1 1]` by defining
`Matrix.etaExpand A` to be equal to the RHS definitionally, and then prove that
`A = eta_expand A`.

The definitions in this file should normally not be used directly; the intent is for the
corresponding `*_eq` lemmas to be used in a place where they are definitionally unfolded.

## Main definitions

* `Matrix.transposeᵣ`
* `Matrix.dotProductᵣ`
* `Matrix.mulᵣ`
* `Matrix.mulVecᵣ`
* `Matrix.vecMulᵣ`
* `Matrix.etaExpand`

-/


open Matrix

namespace Matrix

variable {l m n : ℕ} {α β : Type*}

/-- `∀` with better defeq for `∀ x : Matrix (Fin m) (Fin n) α, P x`. -/
def Forall : ∀ {m n} (_ : Matrix (Fin m) (Fin n) α → Prop), Prop
  | 0, _, P => P (of ![])
  | _ + 1, _, P => FinVec.Forall fun r => Forall fun A => P (of (Matrix.vecCons r A))
#align matrix.forall Matrix.Forall

/-- This can be use to prove
```lean
example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
  (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f] :=
(forall_iff _).symm
```
-/
theorem forall_iff : ∀ {m n} (P : Matrix (Fin m) (Fin n) α → Prop), Forall P ↔ ∀ x, P x
  | 0, n, P => Iff.symm Fin.forall_fin_zero_pi
  | m + 1, n, P => by
    simp only [Forall, FinVec.forall_iff, forall_iff]
    -- ⊢ (∀ (x : Fin n → α) (x_1 : Matrix (Fin (Nat.add m 0)) (Fin n) α), P (↑of (vec …
    exact Iff.symm Fin.forall_fin_succ_pi
    -- 🎉 no goals
#align matrix.forall_iff Matrix.forall_iff

example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
    (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f] :=
  (forall_iff _).symm

/-- `∃` with better defeq for `∃ x : Matrix (Fin m) (Fin n) α, P x`. -/
def Exists : ∀ {m n} (_ : Matrix (Fin m) (Fin n) α → Prop), Prop
  | 0, _, P => P (of ![])
  | _ + 1, _, P => FinVec.Exists fun r => Exists fun A => P (of (Matrix.vecCons r A))
#align matrix.exists Matrix.Exists

/-- This can be use to prove
```lean
example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
  (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f] :=
(exists_iff _).symm
```
-/
theorem exists_iff : ∀ {m n} (P : Matrix (Fin m) (Fin n) α → Prop), Exists P ↔ ∃ x, P x
  | 0, n, P => Iff.symm Fin.exists_fin_zero_pi
  | m + 1, n, P => by
    simp only [Exists, FinVec.exists_iff, exists_iff]
    -- ⊢ (∃ x x_1, P (↑of (vecCons x x_1))) ↔ ∃ x, P x
    exact Iff.symm Fin.exists_fin_succ_pi
    -- 🎉 no goals
#align matrix.exists_iff Matrix.exists_iff

example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
    (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f] :=
  (exists_iff _).symm

/-- `Matrix.transpose` with better defeq for `Fin` -/
def transposeᵣ : ∀ {m n}, Matrix (Fin m) (Fin n) α → Matrix (Fin n) (Fin m) α
  | _, 0, _ => of ![]
  | _, _ + 1, A =>
    of <| vecCons (FinVec.map (fun v : Fin _ → α => v 0) A) (transposeᵣ (A.submatrix id Fin.succ))
#align matrix.transposeᵣ Matrix.transposeᵣ

/-- This can be used to prove
```lean
example (a b c d : α) : transpose !![a, b; c, d] = !![a, c; b, d] := (transposeᵣ_eq _).symm
```
-/
@[simp]
theorem transposeᵣ_eq : ∀ {m n} (A : Matrix (Fin m) (Fin n) α), transposeᵣ A = transpose A
  | _, 0, A => Subsingleton.elim _ _
  | m, n + 1, A =>
    Matrix.ext fun i j => by
      simp_rw [transposeᵣ, transposeᵣ_eq]
      -- ⊢ ↑of (vecCons (FinVec.map (fun v => v 0) A) (submatrix A id Fin.succ)ᵀ) i j = …
      refine' i.cases _ fun i => _
      -- ⊢ ↑of (vecCons (FinVec.map (fun v => v 0) A) (submatrix A id Fin.succ)ᵀ) 0 j = …
      · dsimp
        -- ⊢ FinVec.map (fun v => v 0) A j = A j 0
        rw [FinVec.map_eq, Function.comp_apply]
        -- 🎉 no goals
      · simp only [of_apply, Matrix.cons_val_succ]
        -- ⊢ (submatrix A id Fin.succ)ᵀ i j = Aᵀ (Fin.succ i) j
        rfl
        -- 🎉 no goals
#align matrix.transposeᵣ_eq Matrix.transposeᵣ_eq

example (a b c d : α) : transpose !![a, b; c, d] = !![a, c; b, d] :=
  (transposeᵣ_eq _).symm

/-- `Matrix.dotProduct` with better defeq for `Fin` -/
def dotProductᵣ [Mul α] [Add α] [Zero α] {m} (a b : Fin m → α) : α :=
  FinVec.sum <| FinVec.seq (FinVec.map (· * ·) a) b
#align matrix.dot_productᵣ Matrix.dotProductᵣ

/-- This can be used to prove
```lean
example (a b c d : α) [Mul α] [AddCommMonoid α] :
  dot_product ![a, b] ![c, d] = a * c + b * d :=
(dot_productᵣ_eq _ _).symm
```
-/
@[simp]
theorem dotProductᵣ_eq [Mul α] [AddCommMonoid α] {m} (a b : Fin m → α) :
    dotProductᵣ a b = dotProduct a b := by
  simp_rw [dotProductᵣ, dotProduct, FinVec.sum_eq, FinVec.seq_eq, FinVec.map_eq,
      Function.comp_apply]
#align matrix.dot_productᵣ_eq Matrix.dotProductᵣ_eq

example (a b c d : α) [Mul α] [AddCommMonoid α] : dotProduct ![a, b] ![c, d] = a * c + b * d :=
  (dotProductᵣ_eq _ _).symm

/-- `Matrix.mul` with better defeq for `Fin` -/
def mulᵣ [Mul α] [Add α] [Zero α] (A : Matrix (Fin l) (Fin m) α) (B : Matrix (Fin m) (Fin n) α) :
    Matrix (Fin l) (Fin n) α :=
  of <| FinVec.map (fun v₁ => FinVec.map (fun v₂ => dotProductᵣ v₁ v₂) Bᵀ) A
#align matrix.mulᵣ Matrix.mulᵣ

/-- This can be used to prove
```lean
example [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] * !![b₁₁, b₁₂;
                    b₂₁, b₂₂] =
  !![a₁₁*b₁₁ + a₁₂*b₂₁, a₁₁*b₁₂ + a₁₂*b₂₂;
     a₂₁*b₁₁ + a₂₂*b₂₁, a₂₁*b₁₂ + a₂₂*b₂₂] :=
(mulᵣ_eq _ _).symm
```
-/
@[simp]
theorem mulᵣ_eq [Mul α] [AddCommMonoid α] (A : Matrix (Fin l) (Fin m) α)
    (B : Matrix (Fin m) (Fin n) α) : mulᵣ A B = A * B := by
  simp [mulᵣ, Function.comp, Matrix.transpose]
  -- ⊢ (↑of fun x x_1 => A x ⬝ᵥ ↑of (fun x y => B y x) x_1) = A * B
  rfl
  -- 🎉 no goals
#align matrix.mulᵣ_eq Matrix.mulᵣ_eq

example [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] * !![b₁₁, b₁₂; b₂₁, b₂₂] =
      !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
        a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
  (mulᵣ_eq _ _).symm

/-- `Matrix.mulVec` with better defeq for `Fin` -/
def mulVecᵣ [Mul α] [Add α] [Zero α] (A : Matrix (Fin l) (Fin m) α) (v : Fin m → α) : Fin l → α :=
  FinVec.map (fun a => dotProductᵣ a v) A
#align matrix.mul_vecᵣ Matrix.mulVecᵣ

/-- This can be used to prove
```lean
example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂].mulVec ![b₁, b₂] = ![a₁₁*b₁ + a₁₂*b₂, a₂₁*b₁ + a₂₂*b₂] :=
(mulVecᵣ_eq _ _).symm
```
-/
@[simp]
theorem mulVecᵣ_eq [NonUnitalNonAssocSemiring α] (A : Matrix (Fin l) (Fin m) α) (v : Fin m → α) :
    mulVecᵣ A v = A.mulVec v := by
  simp [mulVecᵣ, Function.comp]
  -- ⊢ (fun x => A x ⬝ᵥ v) = mulVec A v
  rfl
  -- 🎉 no goals
#align matrix.mul_vecᵣ_eq Matrix.mulVecᵣ_eq

example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂].mulVec ![b₁, b₂] = ![a₁₁ * b₁ + a₁₂ * b₂, a₂₁ * b₁ + a₂₂ * b₂] :=
  (mulVecᵣ_eq _ _).symm

/-- `Matrix.vecMul` with better defeq for `Fin` -/
def vecMulᵣ [Mul α] [Add α] [Zero α] (v : Fin l → α) (A : Matrix (Fin l) (Fin m) α) : Fin m → α :=
  FinVec.map (fun a => dotProductᵣ v a) Aᵀ
#align matrix.vec_mulᵣ Matrix.vecMulᵣ

/-- This can be used to prove
```lean
example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
  vecMul ![b₁, b₂] !![a₁₁, a₁₂;
                       a₂₁, a₂₂] = ![b₁*a₁₁ + b₂*a₂₁, b₁*a₁₂ + b₂*a₂₂] :=
(vecMulᵣ_eq _ _).symm
```
-/
@[simp]
theorem vecMulᵣ_eq [NonUnitalNonAssocSemiring α] (v : Fin l → α) (A : Matrix (Fin l) (Fin m) α) :
    vecMulᵣ v A = vecMul v A := by
  simp [vecMulᵣ, Function.comp]
  -- ⊢ (fun x => v ⬝ᵥ Aᵀ x) = vecMul v A
  rfl
  -- 🎉 no goals
#align matrix.vec_mulᵣ_eq Matrix.vecMulᵣ_eq

example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    vecMul ![b₁, b₂] !![a₁₁, a₁₂; a₂₁, a₂₂] = ![b₁ * a₁₁ + b₂ * a₂₁, b₁ * a₁₂ + b₂ * a₂₂] :=
  (vecMulᵣ_eq _ _).symm

/-- Expand `A` to `!![A 0 0, ...; ..., A m n]` -/
def etaExpand {m n} (A : Matrix (Fin m) (Fin n) α) : Matrix (Fin m) (Fin n) α :=
  Matrix.of (FinVec.etaExpand fun i => FinVec.etaExpand fun j => A i j)
#align matrix.eta_expand Matrix.etaExpand

/-- This can be used to prove
```lean
example (A : Matrix (Fin 2) (Fin 2) α) :
  A = !![A 0 0, A 0 1;
         A 1 0, A 1 1] :=
(etaExpand_eq _).symm
```
-/
theorem etaExpand_eq {m n} (A : Matrix (Fin m) (Fin n) α) : etaExpand A = A := by
  simp_rw [etaExpand, FinVec.etaExpand_eq, Matrix.of, Equiv.refl_apply]
  -- 🎉 no goals
#align matrix.eta_expand_eq Matrix.etaExpand_eq

example (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] :=
  (etaExpand_eq _).symm

end Matrix
