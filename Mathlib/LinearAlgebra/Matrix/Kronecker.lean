/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Kronecker product of matrices

This defines the [Kronecker product](https://en.wikipedia.org/wiki/Kronecker_product).

## Main definitions

* `Matrix.kroneckerMap`: A generalization of the Kronecker product: given a map `f : α → β → γ`
  and matrices `A` and `B` with coefficients in `α` and `β`, respectively, it is defined as the
  matrix with coefficients in `γ` such that
  `kroneckerMap f A B (i₁, i₂) (j₁, j₂) = f (A i₁ j₁) (B i₁ j₂)`.
* `Matrix.kroneckerMapBilinear`: when `f` is bilinear, so is `kroneckerMap f`.

## Specializations

* `Matrix.kronecker`: An alias of `kroneckerMap (*)`. Prefer using the notation.
* `Matrix.kroneckerBilinear`: `Matrix.kronecker` is bilinear

* `Matrix.kroneckerTMul`: An alias of `kroneckerMap (⊗ₜ)`. Prefer using the notation.
* `Matrix.kroneckerTMulBilinear`: `Matrix.kroneckerTMul` is bilinear

## Notation

These require `open Kronecker`:

* `A ⊗ₖ B` for `kroneckerMap (*) A B`. Lemmas about this notation use the token `kronecker`.
* `A ⊗ₖₜ B` and `A ⊗ₖₜ[R] B` for `kroneckerMap (⊗ₜ) A B`.
  Lemmas about this notation use the token `kroneckerTMul`.

-/

@[expose] public section


namespace Matrix
open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}
variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

section KroneckerMap

/-- Produce a matrix with `f` applied to every pair of elements from `A` and `B`. -/
def kroneckerMap (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) : Matrix (l × n) (m × p) γ :=
  of fun (i : l × n) (j : m × p) => f (A i.1 j.1) (B i.2 j.2)

-- TODO: set as an equation lemma for `kroneckerMap`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem kroneckerMap_apply (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) (i j) :
    kroneckerMap f A B i j = f (A i.1 j.1) (B i.2 j.2) :=
  rfl

theorem kroneckerMap_transpose (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f Aᵀ Bᵀ = (kroneckerMap f A B)ᵀ :=
  ext fun _ _ => rfl

theorem kroneckerMap_map_left (f : α' → β → γ) (g : α → α') (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (A.map g) B = kroneckerMap (fun a b => f (g a) b) A B :=
  ext fun _ _ => rfl

theorem kroneckerMap_map_right (f : α → β' → γ) (g : β → β') (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f A (B.map g) = kroneckerMap (fun a b => f a (g b)) A B :=
  ext fun _ _ => rfl

theorem kroneckerMap_map (f : α → β → γ) (g : γ → γ') (A : Matrix l m α) (B : Matrix n p β) :
    (kroneckerMap f A B).map g = kroneckerMap (fun a b => g (f a b)) A B :=
  ext fun _ _ => rfl

@[simp]
theorem kroneckerMap_zero_left [Zero α] [Zero γ] (f : α → β → γ) (hf : ∀ b, f 0 b = 0)
    (B : Matrix n p β) : kroneckerMap f (0 : Matrix l m α) B = 0 :=
  ext fun _ _ => hf _

@[simp]
theorem kroneckerMap_zero_right [Zero β] [Zero γ] (f : α → β → γ) (hf : ∀ a, f a 0 = 0)
    (A : Matrix l m α) : kroneckerMap f A (0 : Matrix n p β) = 0 :=
  ext fun _ _ => hf _

theorem kroneckerMap_add_left [Add α] [Add γ] (f : α → β → γ)
    (hf : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b) (A₁ A₂ : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (A₁ + A₂) B = kroneckerMap f A₁ B + kroneckerMap f A₂ B :=
  ext fun _ _ => hf _ _ _

theorem kroneckerMap_add_right [Add β] [Add γ] (f : α → β → γ)
    (hf : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) (A : Matrix l m α) (B₁ B₂ : Matrix n p β) :
    kroneckerMap f A (B₁ + B₂) = kroneckerMap f A B₁ + kroneckerMap f A B₂ :=
  ext fun _ _ => hf _ _ _

theorem kroneckerMap_smul_left [SMul R α] [SMul R γ] (f : α → β → γ) (r : R)
    (hf : ∀ a b, f (r • a) b = r • f a b) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (r • A) B = r • kroneckerMap f A B :=
  ext fun _ _ => hf _ _

theorem kroneckerMap_smul_right [SMul R β] [SMul R γ] (f : α → β → γ) (r : R)
    (hf : ∀ a b, f a (r • b) = r • f a b) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f A (r • B) = r • kroneckerMap f A B :=
  ext fun _ _ => hf _ _

theorem kroneckerMap_single_single
    [Zero α] [Zero β] [Zero γ] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (i₁ : l) (j₁ : m) (i₂ : n) (j₂ : p)
    (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (a : α) (b : β) :
    kroneckerMap f (single i₁ j₁ a) (single i₂ j₂ b) = single (i₁, i₂) (j₁, j₂) (f a b) := by
  ext ⟨i₁', i₂'⟩ ⟨j₁', j₂'⟩
  dsimp [single]
  grind

theorem kroneckerMap_diagonal_diagonal [Zero α] [Zero β] [Zero γ] [DecidableEq m] [DecidableEq n]
    (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (a : m → α) (b : n → β) :
    kroneckerMap f (diagonal a) (diagonal b) = diagonal fun mn => f (a mn.1) (b mn.2) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, apply_ite f, ite_and, ite_apply, apply_ite (f (a i₁)), hf₁, hf₂]

theorem kroneckerMap_diagonal_right [Zero β] [Zero γ] [DecidableEq n] (f : α → β → γ)
    (hf : ∀ a, f a 0 = 0) (A : Matrix l m α) (b : n → β) :
    kroneckerMap f A (diagonal b) = blockDiagonal fun i => A.map fun a => f a (b i) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, blockDiagonal, apply_ite (f (A i₁ j₁)), hf]

theorem kroneckerMap_diagonal_left [Zero α] [Zero γ] [DecidableEq l] (f : α → β → γ)
    (hf : ∀ b, f 0 b = 0) (a : l → α) (B : Matrix m n β) :
    kroneckerMap f (diagonal a) B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
        (blockDiagonal fun i => B.map fun b => f (a i) b) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, blockDiagonal, apply_ite f, ite_apply, hf]

@[simp]
theorem kroneckerMap_one_one [Zero α] [Zero β] [Zero γ] [One α] [One β] [One γ] [DecidableEq m]
    [DecidableEq n] (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0)
    (hf₃ : f 1 1 = 1) : kroneckerMap f (1 : Matrix m m α) (1 : Matrix n n β) = 1 :=
  (kroneckerMap_diagonal_diagonal _ hf₁ hf₂ _ _).trans <| by simp only [hf₃, diagonal_one]

theorem kroneckerMap_reindex (f : α → β → γ) (el : l ≃ l') (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p')
    (M : Matrix l m α) (N : Matrix n p β) :
    kroneckerMap f (reindex el em M) (reindex en ep N) =
      reindex (el.prodCongr en) (em.prodCongr ep) (kroneckerMap f M N) := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  rfl

theorem kroneckerMap_reindex_left (f : α → β → γ) (el : l ≃ l') (em : m ≃ m') (M : Matrix l m α)
    (N : Matrix n n' β) :
    kroneckerMap f (Matrix.reindex el em M) N =
      reindex (el.prodCongr (Equiv.refl _)) (em.prodCongr (Equiv.refl _)) (kroneckerMap f M N) :=
  kroneckerMap_reindex _ _ _ (Equiv.refl _) (Equiv.refl _) _ _

theorem kroneckerMap_reindex_right (f : α → β → γ) (em : m ≃ m') (en : n ≃ n') (M : Matrix l l' α)
    (N : Matrix m n β) :
    kroneckerMap f M (reindex em en N) =
      reindex ((Equiv.refl _).prodCongr em) ((Equiv.refl _).prodCongr en) (kroneckerMap f M N) :=
  kroneckerMap_reindex _ (Equiv.refl _) (Equiv.refl _) _ _ _ _

theorem kroneckerMap_assoc {δ ξ ω ω' : Type*} (f : α → β → γ) (g : γ → δ → ω) (f' : α → ξ → ω')
    (g' : β → δ → ξ) (A : Matrix l m α) (B : Matrix n p β) (D : Matrix q r δ) (φ : ω ≃ ω')
    (hφ : ∀ a b d, φ (g (f a b) d) = f' a (g' b d)) :
    (reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)).trans (Equiv.mapMatrix φ)
        (kroneckerMap g (kroneckerMap f A B) D) =
      kroneckerMap f' A (kroneckerMap g' B D) :=
  ext fun _ _ => hφ _ _ _

theorem kroneckerMap_assoc₁ {δ ξ ω : Type*} (f : α → β → γ) (g : γ → δ → ω) (f' : α → ξ → ω)
    (g' : β → δ → ξ) (A : Matrix l m α) (B : Matrix n p β) (D : Matrix q r δ)
    (h : ∀ a b d, g (f a b) d = f' a (g' b d)) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)
        (kroneckerMap g (kroneckerMap f A B) D) =
      kroneckerMap f' A (kroneckerMap g' B D) :=
  ext fun _ _ => h _ _ _

/-- When `f` is bilinear then `Matrix.kroneckerMap f` is also bilinear. -/
@[simps!]
def kroneckerMapBilinear [Semiring S] [Semiring R]
    [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
    [Module R α] [Module R γ] [Module S β] [Module S γ] [SMulCommClass S R γ]
    (f : α →ₗ[R] β →ₗ[S] γ) :
    Matrix l m α →ₗ[R] Matrix n p β →ₗ[S] Matrix (l × n) (m × p) γ :=
  LinearMap.mk₂' R S (kroneckerMap fun r s => f r s) (kroneckerMap_add_left _ <| f.map_add₂)
    (fun _ => kroneckerMap_smul_left _ _ <| f.map_smul₂ _)
    (kroneckerMap_add_right _ fun a => (f a).map_add) fun r =>
    kroneckerMap_smul_right _ _ fun a => (f a).map_smul r

/-- `Matrix.kroneckerMapBilinear` commutes with `*` if `f` does.

This is primarily used with `R = ℕ` to prove `Matrix.mul_kronecker_mul`. -/
theorem kroneckerMapBilinear_mul_mul [Semiring S] [Semiring R] [Fintype m] [Fintype m']
    [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [NonUnitalNonAssocSemiring γ]
    [Module R α] [Module R γ] [Module S β] [Module S γ] [SMulCommClass S R γ]
    (f : α →ₗ[R] β →ₗ[S] γ)
    (h_comm : ∀ a b a' b', f (a * b) (a' * b') = f a a' * f b b') (A : Matrix l m α)
    (B : Matrix m n α) (A' : Matrix l' m' β) (B' : Matrix m' n' β) :
    kroneckerMapBilinear f (A * B) (A' * B') =
      kroneckerMapBilinear f A A' * kroneckerMapBilinear f B B' := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp only [kroneckerMapBilinear_apply_apply, mul_apply, ← Finset.univ_product_univ,
    Finset.sum_product, kroneckerMap_apply]
  simp_rw [map_sum f, LinearMap.sum_apply, map_sum, h_comm]

/-- `trace` distributes over `Matrix.kroneckerMapBilinear`.

This is primarily used with `R = ℕ` to prove `Matrix.trace_kronecker`. -/
theorem trace_kroneckerMapBilinear [Semiring S] [Semiring R] [Fintype m] [Fintype n]
    [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
    [Module R α] [Module R γ] [Module S β] [Module S γ] [SMulCommClass S R γ]
    (f : α →ₗ[R] β →ₗ[S] γ)
    (A : Matrix m m α) (B : Matrix n n β) :
    trace (kroneckerMapBilinear f A B) = f (trace A) (trace B) := by
  simp_rw [Matrix.trace, Matrix.diag, kroneckerMapBilinear_apply_apply, LinearMap.map_sum₂,
    map_sum, ← Finset.univ_product_univ, Finset.sum_product, kroneckerMap_apply]

/-- `determinant` of `Matrix.kroneckerMapBilinear`.

This is primarily used with `R = ℕ` to prove `Matrix.det_kronecker`. -/
theorem det_kroneckerMapBilinear [Semiring S] [Semiring R] [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [NonAssocSemiring α] [NonAssocSemiring β] [CommRing γ] [Module R α] [Module S β]
    [Module R γ] [Module S γ] [SMulCommClass S R γ]
    (f : α →ₗ[R] β →ₗ[S] γ) (h_comm : ∀ a b a' b', f (a * b) (a' * b') = f a a' * f b b')
    (A : Matrix m m α) (B : Matrix n n β) :
    det (kroneckerMapBilinear f A B) =
      det (A.map fun a => f a 1) ^ Fintype.card n * det (B.map fun b => f 1 b) ^ Fintype.card m :=
  calc
    det (kroneckerMapBilinear f A B) =
        det (kroneckerMapBilinear f A 1 * kroneckerMapBilinear f 1 B) := by
      rw [← kroneckerMapBilinear_mul_mul f h_comm, Matrix.mul_one, Matrix.one_mul]
    _ = det (blockDiagonal fun (_ : n) => A.map fun a => f a 1) *
        det (blockDiagonal fun (_ : m) => B.map fun b => f 1 b) := by
      rw [det_mul, ← diagonal_one, ← diagonal_one, kroneckerMapBilinear_apply_apply,
        kroneckerMap_diagonal_right _ fun _ => _, kroneckerMapBilinear_apply_apply,
        kroneckerMap_diagonal_left _ fun _ => _, det_reindex_self]
      · intro; exact LinearMap.map_zero₂ _ _
      · intro; exact map_zero _
    _ = _ := by simp_rw [det_blockDiagonal, Finset.prod_const, Finset.card_univ]

end KroneckerMap

/-! ### Specialization to `Matrix.kroneckerMap (*)` -/


section Kronecker

open Matrix

/-- The Kronecker product. This is just a shorthand for `kroneckerMap (*)`. Prefer the notation
`⊗ₖ` rather than this definition. -/
@[simp]
def kronecker [Mul α] : Matrix l m α → Matrix n p α → Matrix (l × n) (m × p) α :=
  kroneckerMap (· * ·)

@[inherit_doc Matrix.kroneckerMap]
scoped[Kronecker] infixl:100 " ⊗ₖ " => Matrix.kroneckerMap (· * ·)

open Kronecker

@[simp]
theorem kronecker_apply [Mul α] (A : Matrix l m α) (B : Matrix n p α) (i₁ i₂ j₁ j₂) :
    (A ⊗ₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂ :=
  rfl

/-- `Matrix.kronecker` as a bilinear map. -/
def kroneckerBilinear [CommSemiring R] [Semiring α] [Algebra R α] :
    Matrix l m α →ₗ[R] Matrix n p α →ₗ[R] Matrix (l × n) (m × p) α :=
  kroneckerMapBilinear (Algebra.lmul R α)

/-! What follows is a copy, in order, of every `Matrix.kroneckerMap` lemma above that has
hypotheses which can be filled by properties of `*`. -/


theorem zero_kronecker [MulZeroClass α] (B : Matrix n p α) : (0 : Matrix l m α) ⊗ₖ B = 0 :=
  kroneckerMap_zero_left _ zero_mul B

theorem kronecker_zero [MulZeroClass α] (A : Matrix l m α) : A ⊗ₖ (0 : Matrix n p α) = 0 :=
  kroneckerMap_zero_right _ mul_zero A

theorem add_kronecker [Distrib α] (A₁ A₂ : Matrix l m α) (B : Matrix n p α) :
    (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B :=
  kroneckerMap_add_left _ add_mul _ _ _

theorem kronecker_add [Distrib α] (A : Matrix l m α) (B₁ B₂ : Matrix n p α) :
    A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ :=
  kroneckerMap_add_right _ mul_add _ _ _

theorem smul_kronecker [Mul α] [SMul R α] [IsScalarTower R α α] (r : R)
    (A : Matrix l m α) (B : Matrix n p α) : (r • A) ⊗ₖ B = r • A ⊗ₖ B :=
  kroneckerMap_smul_left _ _ (fun _ _ => smul_mul_assoc _ _ _) _ _

theorem kronecker_smul [Mul α] [SMul R α] [SMulCommClass R α α] (r : R)
    (A : Matrix l m α) (B : Matrix n p α) : A ⊗ₖ (r • B) = r • A ⊗ₖ B :=
  kroneckerMap_smul_right _ _ (fun _ _ => mul_smul_comm _ _ _) _ _

theorem single_kronecker_single
    [MulZeroClass α] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ia : l) (ja : m) (ib : n) (jb : p) (a b : α) :
    single ia ja a ⊗ₖ single ib jb b = single (ia, ib) (ja, jb) (a * b) :=
  kroneckerMap_single_single _ _ _ _ _ zero_mul mul_zero _ _

theorem diagonal_kronecker_diagonal [MulZeroClass α] [DecidableEq m] [DecidableEq n] (a : m → α)
    (b : n → α) : diagonal a ⊗ₖ diagonal b = diagonal fun mn => a mn.1 * b mn.2 :=
  kroneckerMap_diagonal_diagonal _ zero_mul mul_zero _ _

theorem kronecker_diagonal [MulZeroClass α] [DecidableEq n] (A : Matrix l m α) (b : n → α) :
    A ⊗ₖ diagonal b = blockDiagonal fun i => A <• b i :=
  kroneckerMap_diagonal_right _ mul_zero _ _

theorem diagonal_kronecker [MulZeroClass α] [DecidableEq l] (a : l → α) (B : Matrix m n α) :
    diagonal a ⊗ₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun i => a i • B) :=
  kroneckerMap_diagonal_left _ zero_mul _ _

@[simp]
theorem natCast_kronecker_natCast [NonAssocSemiring α] [DecidableEq m] [DecidableEq n] (a b : ℕ) :
    (a : Matrix m m α) ⊗ₖ (b : Matrix n n α) = ↑(a * b) :=
  (diagonal_kronecker_diagonal _ _).trans <| by simp_rw [← Nat.cast_mul]; rfl

theorem kronecker_natCast [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) (b : ℕ) :
    A ⊗ₖ (b : Matrix n n α) = blockDiagonal fun _ => b • A :=
  kronecker_diagonal _ _ |>.trans <| by
    congr! 2
    ext
    simp [(Nat.cast_commute b _).eq]

theorem natCast_kronecker [NonAssocSemiring α] [DecidableEq l] (a : ℕ) (B : Matrix m n α) :
    (a : Matrix l l α) ⊗ₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun _ => a • B) :=
  diagonal_kronecker _ _ |>.trans <| by
    congr! 2
    ext
    simp [(Nat.cast_commute a _).eq]

theorem kronecker_ofNat [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) (b : ℕ)
    [b.AtLeastTwo] : A ⊗ₖ (ofNat(b) : Matrix n n α) =
      blockDiagonal fun _ => A <• (ofNat(b) : α) :=
  kronecker_diagonal _ _

theorem ofNat_kronecker [NonAssocSemiring α] [DecidableEq l] (a : ℕ) [a.AtLeastTwo]
    (B : Matrix m n α) : (ofNat(a) : Matrix l l α) ⊗ₖ B =
      Matrix.reindex (.prodComm _ _) (.prodComm _ _)
        (blockDiagonal fun _ => (ofNat(a) : α) • B) :=
  diagonal_kronecker _ _

theorem one_kronecker_one [MulZeroOneClass α] [DecidableEq m] [DecidableEq n] :
    (1 : Matrix m m α) ⊗ₖ (1 : Matrix n n α) = 1 :=
  kroneckerMap_one_one _ zero_mul mul_zero (one_mul _)

theorem kronecker_one [MulZeroOneClass α] [DecidableEq n] (A : Matrix l m α) :
    A ⊗ₖ (1 : Matrix n n α) = blockDiagonal fun _ => A :=
  (kronecker_diagonal _ _).trans <| congr_arg _ <| funext fun _ => Matrix.ext fun _ _ => mul_one _

theorem one_kronecker [MulZeroOneClass α] [DecidableEq l] (B : Matrix m n α) :
    (1 : Matrix l l α) ⊗ₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun _ => B) :=
  (diagonal_kronecker _ _).trans <|
    congr_arg _ <| congr_arg _ <| funext fun _ => Matrix.ext fun _ _ => one_mul _

theorem mul_kronecker_mul [Fintype m] [Fintype m'] [CommSemiring α] (A : Matrix l m α)
    (B : Matrix m n α) (A' : Matrix l' m' α) (B' : Matrix m' n' α) :
    (A * B) ⊗ₖ (A' * B') = A ⊗ₖ A' * B ⊗ₖ B' :=
  kroneckerMapBilinear_mul_mul (Algebra.lmul ℕ α).toLinearMap mul_mul_mul_comm A B A' B'

-- simp-normal form is `kronecker_assoc'`
theorem kronecker_assoc [Semigroup α] (A : Matrix l m α) (B : Matrix n p α) (C : Matrix q r α) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r) (A ⊗ₖ B ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C) :=
  kroneckerMap_assoc₁ _ _ _ _ A B C mul_assoc

@[simp]
theorem kronecker_assoc' [Semigroup α] (A : Matrix l m α) (B : Matrix n p α) (C : Matrix q r α) :
    submatrix (A ⊗ₖ B ⊗ₖ C) (Equiv.prodAssoc l n q).symm (Equiv.prodAssoc m p r).symm =
    A ⊗ₖ (B ⊗ₖ C) :=
  kroneckerMap_assoc₁ _ _ _ _ A B C mul_assoc

theorem trace_kronecker [Fintype m] [Fintype n] [Semiring α] (A : Matrix m m α) (B : Matrix n n α) :
    trace (A ⊗ₖ B) = trace A * trace B :=
  trace_kroneckerMapBilinear (Algebra.lmul ℕ α).toLinearMap _ _

theorem det_kronecker [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : Matrix m m R) (B : Matrix n n R) :
    det (A ⊗ₖ B) = det A ^ Fintype.card n * det B ^ Fintype.card m := by
  refine (det_kroneckerMapBilinear (Algebra.lmul ℕ R).toLinearMap mul_mul_mul_comm _ _).trans ?_
  simp

theorem conjTranspose_kronecker [CommMagma R] [StarMul R] (x : Matrix l m R) (y : Matrix n p R) :
    (x ⊗ₖ y)ᴴ = xᴴ ⊗ₖ yᴴ := by
  ext; simp

theorem conjTranspose_kronecker' [Mul R] [StarMul R] (x : Matrix l m R) (y : Matrix n p R) :
    (x ⊗ₖ y)ᴴ = (yᴴ ⊗ₖ xᴴ).submatrix Prod.swap Prod.swap := by
  ext; simp

end Kronecker

/-! ### Specialization to `Matrix.kroneckerMap (⊗ₜ)` -/


section KroneckerTmul

variable (R)

open TensorProduct

open Matrix TensorProduct

section Module

variable [CommSemiring R]
variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
variable [Module R α] [Module R β] [Module R γ]

/-- The Kronecker tensor product. This is just a shorthand for `kroneckerMap (⊗ₜ)`.
Prefer the notation `⊗ₖₜ` rather than this definition. -/
@[simp]
def kroneckerTMul : Matrix l m α → Matrix n p β → Matrix (l × n) (m × p) (α ⊗[R] β) :=
  kroneckerMap (· ⊗ₜ ·)

@[inherit_doc kroneckerTMul]
scoped[Kronecker] infixl:100 " ⊗ₖₜ " => Matrix.kroneckerMap (TensorProduct.tmul _)

@[inherit_doc kroneckerTMul] scoped[Kronecker] notation:100 x " ⊗ₖₜ[" R "] " y:100 =>
  Matrix.kroneckerMap (TensorProduct.tmul R) x y

open Kronecker

@[simp]
theorem kroneckerTMul_apply (A : Matrix l m α) (B : Matrix n p β) (i₁ i₂ j₁ j₂) :
    (A ⊗ₖₜ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ ⊗ₜ[R] B i₂ j₂ :=
  rfl

variable (S) in
/-- `Matrix.kronecker` as a bilinear map. -/
def kroneckerTMulBilinear [Semiring S] [Module S α] [SMulCommClass R S α] :
    Matrix l m α →ₗ[S] Matrix n p β →ₗ[R] Matrix (l × n) (m × p) (α ⊗[R] β) :=
  kroneckerMapBilinear (AlgebraTensorModule.mk _ _ α β)

@[simp]
theorem kroneckerTMulBilinear_apply [Semiring S] [Module S α] [SMulCommClass R S α]
    (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerTMulBilinear R S A B = A ⊗ₖₜ[R] B := rfl

/-! What follows is a copy, in order, of every `Matrix.kroneckerMap` lemma above that has
hypotheses which can be filled by properties of `⊗ₜ`. -/


theorem zero_kroneckerTMul (B : Matrix n p β) : (0 : Matrix l m α) ⊗ₖₜ[R] B = 0 :=
  kroneckerMap_zero_left _ (zero_tmul α) B

theorem kroneckerTMul_zero (A : Matrix l m α) : A ⊗ₖₜ[R] (0 : Matrix n p β) = 0 :=
  kroneckerMap_zero_right _ (tmul_zero β) A

theorem add_kroneckerTMul (A₁ A₂ : Matrix l m α) (B : Matrix n p α) :
    (A₁ + A₂) ⊗ₖₜ[R] B = A₁ ⊗ₖₜ B + A₂ ⊗ₖₜ B :=
  kroneckerMap_add_left _ add_tmul _ _ _

theorem kroneckerTMul_add (A : Matrix l m α) (B₁ B₂ : Matrix n p β) :
    A ⊗ₖₜ[R] (B₁ + B₂) = A ⊗ₖₜ B₁ + A ⊗ₖₜ B₂ :=
  kroneckerMap_add_right _ tmul_add _ _ _

theorem smul_kroneckerTMul [Monoid S] [DistribMulAction S α] [SMulCommClass R S α]
    (r : S) (A : Matrix l m α) (B : Matrix n p β) :
    (r • A) ⊗ₖₜ[R] B = r • A ⊗ₖₜ[R] B :=
  kroneckerMap_smul_left _ _ (fun _ _ => smul_tmul' _ _ _) _ _

theorem kroneckerTMul_smul [Monoid S] [DistribMulAction S α] [DistribMulAction S β]
    [SMul S R] [SMulCommClass R S α] [IsScalarTower S R α] [IsScalarTower S R β]
    (r : S) (A : Matrix l m α) (B : Matrix n p β) :
    A ⊗ₖₜ[R] (r • B) = r • A ⊗ₖₜ[R] B :=
  kroneckerMap_smul_right _ _ (fun _ _ => tmul_smul _ _ _) _ _

theorem single_kroneckerTMul_single
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (i₁ : l) (j₁ : m) (i₂ : n) (j₂ : p) (a : α) (b : β) :
    single i₁ j₁ a ⊗ₖₜ[R] single i₂ j₂ b = single (i₁, i₂) (j₁, j₂) (a ⊗ₜ b) :=
  kroneckerMap_single_single _ _ _ _ _ (zero_tmul _) (tmul_zero _) _ _

theorem diagonal_kroneckerTMul_diagonal [DecidableEq m] [DecidableEq n] (a : m → α) (b : n → β) :
    diagonal a ⊗ₖₜ[R] diagonal b = diagonal fun mn => a mn.1 ⊗ₜ b mn.2 :=
  kroneckerMap_diagonal_diagonal _ (zero_tmul _) (tmul_zero _) _ _

theorem kroneckerTMul_diagonal [DecidableEq n] (A : Matrix l m α) (b : n → β) :
    A ⊗ₖₜ[R] diagonal b = blockDiagonal fun i => A.map fun a => a ⊗ₜ[R] b i :=
  kroneckerMap_diagonal_right _ (tmul_zero _) _ _

theorem diagonal_kroneckerTMul [DecidableEq l] (a : l → α) (B : Matrix m n β) :
    diagonal a ⊗ₖₜ[R] B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
        (blockDiagonal fun i => B.map fun b => a i ⊗ₜ[R] b) :=
  kroneckerMap_diagonal_left _ (zero_tmul _) _ _

-- simp-normal form is `kroneckerTMul_assoc'`
theorem kroneckerTMul_assoc (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r γ) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)
        (((A ⊗ₖₜ[R] B) ⊗ₖₜ[R] C).map (TensorProduct.assoc R α β γ)) =
      A ⊗ₖₜ[R] B ⊗ₖₜ[R] C :=
  ext fun _ _ => assoc_tmul _ _ _

@[simp]
theorem kroneckerTMul_assoc' (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r γ) :
    submatrix (((A ⊗ₖₜ[R] B) ⊗ₖₜ[R] C).map (TensorProduct.assoc R α β γ))
      (Equiv.prodAssoc l n q).symm (Equiv.prodAssoc m p r).symm = A ⊗ₖₜ[R] B ⊗ₖₜ[R] C :=
  ext fun _ _ => assoc_tmul _ _ _

theorem trace_kroneckerTMul [Fintype m] [Fintype n] (A : Matrix m m α) (B : Matrix n n β) :
    trace (A ⊗ₖₜ[R] B) = trace A ⊗ₜ[R] trace B :=
  trace_kroneckerMapBilinear (TensorProduct.mk R α β) _ _

theorem conjTranspose_kroneckerTMul [StarRing R] [StarAddMonoid α] [StarAddMonoid β]
    [StarModule R α] [StarModule R β] (x : Matrix l m α) (y : Matrix n p β) :
    (x ⊗ₖₜ[R] y)ᴴ = xᴴ ⊗ₖₜ[R] yᴴ := by
  ext; simp

end Module

section Algebra

open Kronecker

open Algebra.TensorProduct

section Semiring
variable [CommSemiring R]

@[simp]
theorem one_kroneckerTMul_one
    [AddCommMonoidWithOne α] [AddCommMonoidWithOne β] [Module R α] [Module R β]
    [DecidableEq m] [DecidableEq n] :
    (1 : Matrix m m α) ⊗ₖₜ[R] (1 : Matrix n n β) = 1 :=
  kroneckerMap_one_one _ (zero_tmul _) (tmul_zero _) rfl

unseal mul in
theorem mul_kroneckerTMul_mul
    [NonUnitalSemiring α] [NonUnitalSemiring β] [Module R α] [Module R β]
    [IsScalarTower R α α] [SMulCommClass R α α] [IsScalarTower R β β] [SMulCommClass R β β]
    [Fintype m] [Fintype m'] (A : Matrix l m α) (B : Matrix m n α)
    (A' : Matrix l' m' β) (B' : Matrix m' n' β) :
    (A * B) ⊗ₖₜ[R] (A' * B') = A ⊗ₖₜ[R] A' * B ⊗ₖₜ[R] B' :=
  kroneckerMapBilinear_mul_mul (TensorProduct.mk R α β) tmul_mul_tmul A B A' B'

end Semiring

section CommRing

variable [CommRing R] [CommRing α] [CommRing β] [Algebra R α] [Algebra R β]

unseal mul in
theorem det_kroneckerTMul [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m α) (B : Matrix n n β) :
    det (A ⊗ₖₜ[R] B) = (det A ^ Fintype.card n) ⊗ₜ[R] (det B ^ Fintype.card m) := by
  refine (det_kroneckerMapBilinear (TensorProduct.mk R α β) tmul_mul_tmul _ _).trans ?_
  simp -eta only [mk_apply, ← includeLeft_apply (S := R), ← includeRight_apply]
  simp only [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  simp only [includeLeft_apply, includeRight_apply, tmul_pow, tmul_mul_tmul, one_pow,
    _root_.mul_one, _root_.one_mul]

end CommRing

end Algebra

-- insert lemmas specific to `kroneckerTMul` below this line
end KroneckerTmul

end Matrix
