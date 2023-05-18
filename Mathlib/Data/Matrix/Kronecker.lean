/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Eric Wieser

! This file was ported from Lean 3 source module data.matrix.kronecker
! leanprover-community/mathlib commit 3e068ece210655b7b9a9477c3aff38a492400aa1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.Data.Matrix.Block
import Mathbin.LinearAlgebra.Matrix.Determinant
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.TensorProduct
import Mathbin.RingTheory.TensorProduct

/-!
# Kronecker product of matrices

This defines the [Kronecker product](https://en.wikipedia.org/wiki/Kronecker_product).

## Main definitions

* `matrix.kronecker_map`: A generalization of the Kronecker product: given a map `f : α → β → γ`
  and matrices `A` and `B` with coefficients in `α` and `β`, respectively, it is defined as the
  matrix with coefficients in `γ` such that
  `kronecker_map f A B (i₁, i₂) (j₁, j₂) = f (A i₁ j₁) (B i₁ j₂)`.
* `matrix.kronecker_map_bilinear`: when `f` is bilinear, so is `kronecker_map f`.

## Specializations

* `matrix.kronecker`: An alias of `kronecker_map (*)`. Prefer using the notation.
* `matrix.kronecker_bilinear`: `matrix.kronecker` is bilinear

* `matrix.kronecker_tmul`: An alias of `kronecker_map (⊗ₜ)`. Prefer using the notation.
* `matrix.kronecker_tmul_bilinear`: `matrix.tmul_kronecker` is bilinear

## Notations

These require `open_locale kronecker`:

* `A ⊗ₖ B` for `kronecker_map (*) A B`. Lemmas about this notation use the token `kronecker`.
* `A ⊗ₖₜ B` and `A ⊗ₖₜ[R] B` for `kronecker_map (⊗ₜ) A B`.  Lemmas about this notation use the token
  `kronecker_tmul`.

-/


namespace Matrix

open Matrix

variable {R α α' β β' γ γ' : Type _}

variable {l m n p : Type _} {q r : Type _} {l' m' n' p' : Type _}

section KroneckerMap

/-- Produce a matrix with `f` applied to every pair of elements from `A` and `B`. -/
def kroneckerMap (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) : Matrix (l × n) (m × p) γ :=
  of fun (i : l × n) (j : m × p) => f (A i.1 j.1) (B i.2 j.2)
#align matrix.kronecker_map Matrix.kroneckerMap

-- TODO: set as an equation lemma for `kronecker_map`, see mathlib4#3024
@[simp]
theorem kroneckerMap_apply (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) (i j) :
    kroneckerMap f A B i j = f (A i.1 j.1) (B i.2 j.2) :=
  rfl
#align matrix.kronecker_map_apply Matrix.kroneckerMap_apply

theorem kroneckerMap_transpose (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f Aᵀ Bᵀ = (kroneckerMap f A B)ᵀ :=
  ext fun i j => rfl
#align matrix.kronecker_map_transpose Matrix.kroneckerMap_transpose

theorem kroneckerMap_map_left (f : α' → β → γ) (g : α → α') (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (A.map g) B = kroneckerMap (fun a b => f (g a) b) A B :=
  ext fun i j => rfl
#align matrix.kronecker_map_map_left Matrix.kroneckerMap_map_left

theorem kroneckerMap_map_right (f : α → β' → γ) (g : β → β') (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f A (B.map g) = kroneckerMap (fun a b => f a (g b)) A B :=
  ext fun i j => rfl
#align matrix.kronecker_map_map_right Matrix.kroneckerMap_map_right

theorem kroneckerMap_map (f : α → β → γ) (g : γ → γ') (A : Matrix l m α) (B : Matrix n p β) :
    (kroneckerMap f A B).map g = kroneckerMap (fun a b => g (f a b)) A B :=
  ext fun i j => rfl
#align matrix.kronecker_map_map Matrix.kroneckerMap_map

@[simp]
theorem kroneckerMap_zero_left [Zero α] [Zero γ] (f : α → β → γ) (hf : ∀ b, f 0 b = 0)
    (B : Matrix n p β) : kroneckerMap f (0 : Matrix l m α) B = 0 :=
  ext fun i j => hf _
#align matrix.kronecker_map_zero_left Matrix.kroneckerMap_zero_left

@[simp]
theorem kroneckerMap_zero_right [Zero β] [Zero γ] (f : α → β → γ) (hf : ∀ a, f a 0 = 0)
    (A : Matrix l m α) : kroneckerMap f A (0 : Matrix n p β) = 0 :=
  ext fun i j => hf _
#align matrix.kronecker_map_zero_right Matrix.kroneckerMap_zero_right

theorem kroneckerMap_add_left [Add α] [Add γ] (f : α → β → γ)
    (hf : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b) (A₁ A₂ : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (A₁ + A₂) B = kroneckerMap f A₁ B + kroneckerMap f A₂ B :=
  ext fun i j => hf _ _ _
#align matrix.kronecker_map_add_left Matrix.kroneckerMap_add_left

theorem kroneckerMap_add_right [Add β] [Add γ] (f : α → β → γ)
    (hf : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) (A : Matrix l m α) (B₁ B₂ : Matrix n p β) :
    kroneckerMap f A (B₁ + B₂) = kroneckerMap f A B₁ + kroneckerMap f A B₂ :=
  ext fun i j => hf _ _ _
#align matrix.kronecker_map_add_right Matrix.kroneckerMap_add_right

theorem kroneckerMap_smul_left [SMul R α] [SMul R γ] (f : α → β → γ) (r : R)
    (hf : ∀ a b, f (r • a) b = r • f a b) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f (r • A) B = r • kroneckerMap f A B :=
  ext fun i j => hf _ _
#align matrix.kronecker_map_smul_left Matrix.kroneckerMap_smul_left

theorem kroneckerMap_smul_right [SMul R β] [SMul R γ] (f : α → β → γ) (r : R)
    (hf : ∀ a b, f a (r • b) = r • f a b) (A : Matrix l m α) (B : Matrix n p β) :
    kroneckerMap f A (r • B) = r • kroneckerMap f A B :=
  ext fun i j => hf _ _
#align matrix.kronecker_map_smul_right Matrix.kroneckerMap_smul_right

theorem kroneckerMap_diagonal_diagonal [Zero α] [Zero β] [Zero γ] [DecidableEq m] [DecidableEq n]
    (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (a : m → α) (b : n → β) :
    kroneckerMap f (diagonal a) (diagonal b) = diagonal fun mn => f (a mn.1) (b mn.2) :=
  by
  ext (⟨i₁, i₂⟩⟨j₁, j₂⟩)
  simp [diagonal, apply_ite f, ite_and, ite_apply, apply_ite (f (a i₁)), hf₁, hf₂]
#align matrix.kronecker_map_diagonal_diagonal Matrix.kroneckerMap_diagonal_diagonal

theorem kroneckerMap_diagonal_right [Zero β] [Zero γ] [DecidableEq n] (f : α → β → γ)
    (hf : ∀ a, f a 0 = 0) (A : Matrix l m α) (b : n → β) :
    kroneckerMap f A (diagonal b) = blockDiagonal fun i => A.map fun a => f a (b i) :=
  by
  ext (⟨i₁, i₂⟩⟨j₁, j₂⟩)
  simp [diagonal, block_diagonal, apply_ite (f (A i₁ j₁)), hf]
#align matrix.kronecker_map_diagonal_right Matrix.kroneckerMap_diagonal_right

theorem kroneckerMap_diagonal_left [Zero α] [Zero γ] [DecidableEq l] (f : α → β → γ)
    (hf : ∀ b, f 0 b = 0) (a : l → α) (B : Matrix m n β) :
    kroneckerMap f (diagonal a) B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
        (blockDiagonal fun i => B.map fun b => f (a i) b) :=
  by
  ext (⟨i₁, i₂⟩⟨j₁, j₂⟩)
  simp [diagonal, block_diagonal, apply_ite f, ite_apply, hf]
#align matrix.kronecker_map_diagonal_left Matrix.kroneckerMap_diagonal_left

@[simp]
theorem kroneckerMap_one_one [Zero α] [Zero β] [Zero γ] [One α] [One β] [One γ] [DecidableEq m]
    [DecidableEq n] (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0)
    (hf₃ : f 1 1 = 1) : kroneckerMap f (1 : Matrix m m α) (1 : Matrix n n β) = 1 :=
  (kroneckerMap_diagonal_diagonal _ hf₁ hf₂ _ _).trans <| by simp only [hf₃, diagonal_one]
#align matrix.kronecker_map_one_one Matrix.kroneckerMap_one_one

theorem kroneckerMap_reindex (f : α → β → γ) (el : l ≃ l') (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p')
    (M : Matrix l m α) (N : Matrix n p β) :
    kroneckerMap f (reindex el em M) (reindex en ep N) =
      reindex (el.prodCongr en) (em.prodCongr ep) (kroneckerMap f M N) :=
  by
  ext (⟨i, i'⟩⟨j, j'⟩)
  rfl
#align matrix.kronecker_map_reindex Matrix.kroneckerMap_reindex

theorem kroneckerMap_reindex_left (f : α → β → γ) (el : l ≃ l') (em : m ≃ m') (M : Matrix l m α)
    (N : Matrix n n' β) :
    kroneckerMap f (Matrix.reindex el em M) N =
      reindex (el.prodCongr (Equiv.refl _)) (em.prodCongr (Equiv.refl _)) (kroneckerMap f M N) :=
  kroneckerMap_reindex _ _ _ (Equiv.refl _) (Equiv.refl _) _ _
#align matrix.kronecker_map_reindex_left Matrix.kroneckerMap_reindex_left

theorem kroneckerMap_reindex_right (f : α → β → γ) (em : m ≃ m') (en : n ≃ n') (M : Matrix l l' α)
    (N : Matrix m n β) :
    kroneckerMap f M (reindex em en N) =
      reindex ((Equiv.refl _).prodCongr em) ((Equiv.refl _).prodCongr en) (kroneckerMap f M N) :=
  kroneckerMap_reindex _ (Equiv.refl _) (Equiv.refl _) _ _ _ _
#align matrix.kronecker_map_reindex_right Matrix.kroneckerMap_reindex_right

theorem kroneckerMap_assoc {δ ξ ω ω' : Type _} (f : α → β → γ) (g : γ → δ → ω) (f' : α → ξ → ω')
    (g' : β → δ → ξ) (A : Matrix l m α) (B : Matrix n p β) (D : Matrix q r δ) (φ : ω ≃ ω')
    (hφ : ∀ a b d, φ (g (f a b) d) = f' a (g' b d)) :
    (reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)).trans (Equiv.mapMatrix φ)
        (kroneckerMap g (kroneckerMap f A B) D) =
      kroneckerMap f' A (kroneckerMap g' B D) :=
  ext fun i j => hφ _ _ _
#align matrix.kronecker_map_assoc Matrix.kroneckerMap_assoc

theorem kroneckerMap_assoc₁ {δ ξ ω : Type _} (f : α → β → γ) (g : γ → δ → ω) (f' : α → ξ → ω)
    (g' : β → δ → ξ) (A : Matrix l m α) (B : Matrix n p β) (D : Matrix q r δ)
    (h : ∀ a b d, g (f a b) d = f' a (g' b d)) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)
        (kroneckerMap g (kroneckerMap f A B) D) =
      kroneckerMap f' A (kroneckerMap g' B D) :=
  ext fun i j => h _ _ _
#align matrix.kronecker_map_assoc₁ Matrix.kroneckerMap_assoc₁

/-- When `f` is bilinear then `matrix.kronecker_map f` is also bilinear. -/
@[simps]
def kroneckerMapBilinear [CommSemiring R] [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]
    [Module R α] [Module R β] [Module R γ] (f : α →ₗ[R] β →ₗ[R] γ) :
    Matrix l m α →ₗ[R] Matrix n p β →ₗ[R] Matrix (l × n) (m × p) γ :=
  LinearMap.mk₂ R (kroneckerMap fun r s => f r s) (kroneckerMap_add_left _ <| f.map_add₂)
    (fun r => kroneckerMap_smul_left _ _ <| f.map_smul₂ _)
    (kroneckerMap_add_right _ fun a => (f a).map_add) fun r =>
    kroneckerMap_smul_right _ _ fun a => (f a).map_smul r
#align matrix.kronecker_map_bilinear Matrix.kroneckerMapBilinear

/-- `matrix.kronecker_map_bilinear` commutes with `⬝` if `f` commutes with `*`.

This is primarily used with `R = ℕ` to prove `matrix.mul_kronecker_mul`. -/
theorem kroneckerMapBilinear_mul_mul [CommSemiring R] [Fintype m] [Fintype m']
    [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [NonUnitalNonAssocSemiring γ]
    [Module R α] [Module R β] [Module R γ] (f : α →ₗ[R] β →ₗ[R] γ)
    (h_comm : ∀ a b a' b', f (a * b) (a' * b') = f a a' * f b b') (A : Matrix l m α)
    (B : Matrix m n α) (A' : Matrix l' m' β) (B' : Matrix m' n' β) :
    kroneckerMapBilinear f (A ⬝ B) (A' ⬝ B') =
      kroneckerMapBilinear f A A' ⬝ kroneckerMapBilinear f B B' :=
  by
  ext (⟨i, i'⟩⟨j, j'⟩)
  simp only [kronecker_map_bilinear_apply_apply, mul_apply, ← Finset.univ_product_univ,
    Finset.sum_product, kronecker_map_apply]
  simp_rw [f.map_sum, LinearMap.sum_apply, LinearMap.map_sum, h_comm]
#align matrix.kronecker_map_bilinear_mul_mul Matrix.kroneckerMapBilinear_mul_mul

/-- `trace` distributes over `matrix.kronecker_map_bilinear`.

This is primarily used with `R = ℕ` to prove `matrix.trace_kronecker`. -/
theorem trace_kroneckerMapBilinear [CommSemiring R] [Fintype m] [Fintype n] [AddCommMonoid α]
    [AddCommMonoid β] [AddCommMonoid γ] [Module R α] [Module R β] [Module R γ]
    (f : α →ₗ[R] β →ₗ[R] γ) (A : Matrix m m α) (B : Matrix n n β) :
    trace (kroneckerMapBilinear f A B) = f (trace A) (trace B) := by
  simp_rw [Matrix.trace, Matrix.diag, kronecker_map_bilinear_apply_apply, LinearMap.map_sum₂,
    map_sum, ← Finset.univ_product_univ, Finset.sum_product, kronecker_map_apply]
#align matrix.trace_kronecker_map_bilinear Matrix.trace_kroneckerMapBilinear

/-- `determinant` of `matrix.kronecker_map_bilinear`.

This is primarily used with `R = ℕ` to prove `matrix.det_kronecker`. -/
theorem det_kroneckerMapBilinear [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [CommRing α] [CommRing β] [CommRing γ] [Module R α] [Module R β] [Module R γ]
    (f : α →ₗ[R] β →ₗ[R] γ) (h_comm : ∀ a b a' b', f (a * b) (a' * b') = f a a' * f b b')
    (A : Matrix m m α) (B : Matrix n n β) :
    det (kroneckerMapBilinear f A B) =
      det (A.map fun a => f a 1) ^ Fintype.card n * det (B.map fun b => f 1 b) ^ Fintype.card m :=
  calc
    det (kroneckerMapBilinear f A B) =
        det (kroneckerMapBilinear f A 1 ⬝ kroneckerMapBilinear f 1 B) :=
      by rw [← kronecker_map_bilinear_mul_mul f h_comm, Matrix.mul_one, Matrix.one_mul]
    _ =
        det (blockDiagonal fun _ => A.map fun a => f a 1) *
          det (blockDiagonal fun _ => B.map fun b => f 1 b) :=
      by
      rw [det_mul, ← diagonal_one, ← diagonal_one, kronecker_map_bilinear_apply_apply,
        kronecker_map_diagonal_right _ fun _ => _, kronecker_map_bilinear_apply_apply,
        kronecker_map_diagonal_left _ fun _ => _, det_reindex_self]
      · exact LinearMap.map_zero₂ _ _
      · exact map_zero _
    _ = _ := by simp_rw [det_block_diagonal, Finset.prod_const, Finset.card_univ]
    
#align matrix.det_kronecker_map_bilinear Matrix.det_kroneckerMapBilinear

end KroneckerMap

/-! ### Specialization to `matrix.kronecker_map (*)` -/


section Kronecker

open Matrix

/-- The Kronecker product. This is just a shorthand for `kronecker_map (*)`. Prefer the notation
`⊗ₖ` rather than this definition. -/
@[simp]
def kronecker [Mul α] : Matrix l m α → Matrix n p α → Matrix (l × n) (m × p) α :=
  kroneckerMap (· * ·)
#align matrix.kronecker Matrix.kronecker

-- mathport name: matrix.kronecker_map.mul
scoped[Kronecker] infixl:100 " ⊗ₖ " => Matrix.kroneckerMap (· * ·)

@[simp]
theorem kronecker_apply [Mul α] (A : Matrix l m α) (B : Matrix n p α) (i₁ i₂ j₁ j₂) :
    (A ⊗ₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂ :=
  rfl
#align matrix.kronecker_apply Matrix.kronecker_apply

/-- `matrix.kronecker` as a bilinear map. -/
def kroneckerBilinear [CommSemiring R] [Semiring α] [Algebra R α] :
    Matrix l m α →ₗ[R] Matrix n p α →ₗ[R] Matrix (l × n) (m × p) α :=
  kroneckerMapBilinear (Algebra.lmul R α)
#align matrix.kronecker_bilinear Matrix.kroneckerBilinear

/-! What follows is a copy, in order, of every `matrix.kronecker_map` lemma above that has
hypotheses which can be filled by properties of `*`. -/


@[simp]
theorem zero_kronecker [MulZeroClass α] (B : Matrix n p α) : (0 : Matrix l m α) ⊗ₖ B = 0 :=
  kroneckerMap_zero_left _ MulZeroClass.zero_mul B
#align matrix.zero_kronecker Matrix.zero_kronecker

@[simp]
theorem kronecker_zero [MulZeroClass α] (A : Matrix l m α) : A ⊗ₖ (0 : Matrix n p α) = 0 :=
  kroneckerMap_zero_right _ MulZeroClass.mul_zero A
#align matrix.kronecker_zero Matrix.kronecker_zero

theorem add_kronecker [Distrib α] (A₁ A₂ : Matrix l m α) (B : Matrix n p α) :
    (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B :=
  kroneckerMap_add_left _ add_mul _ _ _
#align matrix.add_kronecker Matrix.add_kronecker

theorem kronecker_add [Distrib α] (A : Matrix l m α) (B₁ B₂ : Matrix n p α) :
    A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ :=
  kroneckerMap_add_right _ mul_add _ _ _
#align matrix.kronecker_add Matrix.kronecker_add

theorem smul_kronecker [Monoid R] [Monoid α] [MulAction R α] [IsScalarTower R α α] (r : R)
    (A : Matrix l m α) (B : Matrix n p α) : (r • A) ⊗ₖ B = r • A ⊗ₖ B :=
  kroneckerMap_smul_left _ _ (fun _ _ => smul_mul_assoc _ _ _) _ _
#align matrix.smul_kronecker Matrix.smul_kronecker

theorem kronecker_smul [Monoid R] [Monoid α] [MulAction R α] [SMulCommClass R α α] (r : R)
    (A : Matrix l m α) (B : Matrix n p α) : A ⊗ₖ (r • B) = r • A ⊗ₖ B :=
  kroneckerMap_smul_right _ _ (fun _ _ => mul_smul_comm _ _ _) _ _
#align matrix.kronecker_smul Matrix.kronecker_smul

theorem diagonal_kronecker_diagonal [MulZeroClass α] [DecidableEq m] [DecidableEq n] (a : m → α)
    (b : n → α) : diagonal a ⊗ₖ diagonal b = diagonal fun mn => a mn.1 * b mn.2 :=
  kroneckerMap_diagonal_diagonal _ MulZeroClass.zero_mul MulZeroClass.mul_zero _ _
#align matrix.diagonal_kronecker_diagonal Matrix.diagonal_kronecker_diagonal

theorem kronecker_diagonal [MulZeroClass α] [DecidableEq n] (A : Matrix l m α) (b : n → α) :
    A ⊗ₖ diagonal b = blockDiagonal fun i => MulOpposite.op (b i) • A :=
  kroneckerMap_diagonal_right _ MulZeroClass.mul_zero _ _
#align matrix.kronecker_diagonal Matrix.kronecker_diagonal

theorem diagonal_kronecker [MulZeroClass α] [DecidableEq l] (a : l → α) (B : Matrix m n α) :
    diagonal a ⊗ₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun i => a i • B) :=
  kroneckerMap_diagonal_left _ MulZeroClass.zero_mul _ _
#align matrix.diagonal_kronecker Matrix.diagonal_kronecker

@[simp]
theorem one_kronecker_one [MulZeroOneClass α] [DecidableEq m] [DecidableEq n] :
    (1 : Matrix m m α) ⊗ₖ (1 : Matrix n n α) = 1 :=
  kroneckerMap_one_one _ MulZeroClass.zero_mul MulZeroClass.mul_zero (one_mul _)
#align matrix.one_kronecker_one Matrix.one_kronecker_one

theorem kronecker_one [MulZeroOneClass α] [DecidableEq n] (A : Matrix l m α) :
    A ⊗ₖ (1 : Matrix n n α) = blockDiagonal fun i => A :=
  (kronecker_diagonal _ _).trans <| congr_arg _ <| funext fun _ => Matrix.ext fun _ _ => mul_one _
#align matrix.kronecker_one Matrix.kronecker_one

theorem one_kronecker [MulZeroOneClass α] [DecidableEq l] (B : Matrix m n α) :
    (1 : Matrix l l α) ⊗ₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun i => B) :=
  (diagonal_kronecker _ _).trans <|
    congr_arg _ <| congr_arg _ <| funext fun _ => Matrix.ext fun _ _ => one_mul _
#align matrix.one_kronecker Matrix.one_kronecker

theorem mul_kronecker_mul [Fintype m] [Fintype m'] [CommSemiring α] (A : Matrix l m α)
    (B : Matrix m n α) (A' : Matrix l' m' α) (B' : Matrix m' n' α) :
    (A ⬝ B) ⊗ₖ (A' ⬝ B') = A ⊗ₖ A' ⬝ B ⊗ₖ B' :=
  kroneckerMapBilinear_mul_mul (Algebra.lmul ℕ α).toLinearMap mul_mul_mul_comm A B A' B'
#align matrix.mul_kronecker_mul Matrix.mul_kronecker_mul

@[simp]
theorem kronecker_assoc [Semigroup α] (A : Matrix l m α) (B : Matrix n p α) (C : Matrix q r α) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r) (A ⊗ₖ B ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C) :=
  kroneckerMap_assoc₁ _ _ _ _ A B C mul_assoc
#align matrix.kronecker_assoc Matrix.kronecker_assoc

theorem trace_kronecker [Fintype m] [Fintype n] [Semiring α] (A : Matrix m m α) (B : Matrix n n α) :
    trace (A ⊗ₖ B) = trace A * trace B :=
  trace_kroneckerMapBilinear (Algebra.lmul ℕ α).toLinearMap _ _
#align matrix.trace_kronecker Matrix.trace_kronecker

theorem det_kronecker [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : Matrix m m R) (B : Matrix n n R) :
    det (A ⊗ₖ B) = det A ^ Fintype.card n * det B ^ Fintype.card m :=
  by
  refine' (det_kronecker_map_bilinear (Algebra.lmul ℕ R).toLinearMap mul_mul_mul_comm _ _).trans _
  congr 3
  · ext (i j)
    exact mul_one _
  · ext (i j)
    exact one_mul _
#align matrix.det_kronecker Matrix.det_kronecker

theorem inv_kronecker [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : Matrix m m R) (B : Matrix n n R) : (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ :=
  by
  -- handle the special cases where either matrix is not invertible
  by_cases hA : IsUnit A.det;
  swap
  · cases isEmpty_or_nonempty n
    · exact Subsingleton.elim _ _
    have hAB : ¬IsUnit (A ⊗ₖ B).det :=
      by
      refine' mt (fun hAB => _) hA
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_left hAB)
    rw [nonsing_inv_apply_not_is_unit _ hA, zero_kronecker, nonsing_inv_apply_not_is_unit _ hAB]
  by_cases hB : IsUnit B.det; swap
  · cases isEmpty_or_nonempty m
    · exact Subsingleton.elim _ _
    have hAB : ¬IsUnit (A ⊗ₖ B).det :=
      by
      refine' mt (fun hAB => _) hB
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_right hAB)
    rw [nonsing_inv_apply_not_is_unit _ hB, kronecker_zero, nonsing_inv_apply_not_is_unit _ hAB]
  -- otherwise follows trivially from `mul_kronecker_mul`
  · apply inv_eq_right_inv
    rw [← mul_kronecker_mul, ← one_kronecker_one, mul_nonsing_inv _ hA, mul_nonsing_inv _ hB]
#align matrix.inv_kronecker Matrix.inv_kronecker

end Kronecker

/-! ### Specialization to `matrix.kronecker_map (⊗ₜ)` -/


section KroneckerTmul

variable (R)

open TensorProduct

open Matrix TensorProduct

section Module

variable [CommSemiring R] [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]

variable [Module R α] [Module R β] [Module R γ]

/-- The Kronecker tensor product. This is just a shorthand for `kronecker_map (⊗ₜ)`.
Prefer the notation `⊗ₖₜ` rather than this definition. -/
@[simp]
def kroneckerTmul : Matrix l m α → Matrix n p β → Matrix (l × n) (m × p) (α ⊗[R] β) :=
  kroneckerMap (· ⊗ₜ ·)
#align matrix.kronecker_tmul Matrix.kroneckerTmul

-- mathport name: matrix.kronecker_map.tmul
scoped[Kronecker] infixl:100 " ⊗ₖₜ " => Matrix.kroneckerMap (· ⊗ₜ ·)

-- mathport name: matrix.kronecker_map.tmul'
scoped[Kronecker]
  notation:100 x " ⊗ₖₜ[" R "] " y:100 => Matrix.kroneckerMap (TensorProduct.tmul R) x y

@[simp]
theorem kronecker_tmul_apply (A : Matrix l m α) (B : Matrix n p β) (i₁ i₂ j₁ j₂) :
    (A ⊗ₖₜ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ ⊗ₜ[R] B i₂ j₂ :=
  rfl
#align matrix.kronecker_tmul_apply Matrix.kronecker_tmul_apply

/-- `matrix.kronecker` as a bilinear map. -/
def kroneckerTmulBilinear :
    Matrix l m α →ₗ[R] Matrix n p β →ₗ[R] Matrix (l × n) (m × p) (α ⊗[R] β) :=
  kroneckerMapBilinear (TensorProduct.mk R α β)
#align matrix.kronecker_tmul_bilinear Matrix.kroneckerTmulBilinear

/-! What follows is a copy, in order, of every `matrix.kronecker_map` lemma above that has
hypotheses which can be filled by properties of `⊗ₜ`. -/


@[simp]
theorem zero_kronecker_tmul (B : Matrix n p β) : (0 : Matrix l m α) ⊗ₖₜ[R] B = 0 :=
  kroneckerMap_zero_left _ (zero_tmul α) B
#align matrix.zero_kronecker_tmul Matrix.zero_kronecker_tmul

@[simp]
theorem kronecker_tmul_zero (A : Matrix l m α) : A ⊗ₖₜ[R] (0 : Matrix n p β) = 0 :=
  kroneckerMap_zero_right _ (tmul_zero β) A
#align matrix.kronecker_tmul_zero Matrix.kronecker_tmul_zero

theorem add_kronecker_tmul (A₁ A₂ : Matrix l m α) (B : Matrix n p α) :
    (A₁ + A₂) ⊗ₖₜ[R] B = A₁ ⊗ₖₜ B + A₂ ⊗ₖₜ B :=
  kroneckerMap_add_left _ add_tmul _ _ _
#align matrix.add_kronecker_tmul Matrix.add_kronecker_tmul

theorem kronecker_tmul_add (A : Matrix l m α) (B₁ B₂ : Matrix n p α) :
    A ⊗ₖₜ[R] (B₁ + B₂) = A ⊗ₖₜ B₁ + A ⊗ₖₜ B₂ :=
  kroneckerMap_add_right _ tmul_add _ _ _
#align matrix.kronecker_tmul_add Matrix.kronecker_tmul_add

theorem smul_kronecker_tmul (r : R) (A : Matrix l m α) (B : Matrix n p α) :
    (r • A) ⊗ₖₜ[R] B = r • A ⊗ₖₜ B :=
  kroneckerMap_smul_left _ _ (fun _ _ => smul_tmul' _ _ _) _ _
#align matrix.smul_kronecker_tmul Matrix.smul_kronecker_tmul

theorem kronecker_tmul_smul (r : R) (A : Matrix l m α) (B : Matrix n p α) :
    A ⊗ₖₜ[R] (r • B) = r • A ⊗ₖₜ B :=
  kroneckerMap_smul_right _ _ (fun _ _ => tmul_smul _ _ _) _ _
#align matrix.kronecker_tmul_smul Matrix.kronecker_tmul_smul

theorem diagonal_kronecker_tmul_diagonal [DecidableEq m] [DecidableEq n] (a : m → α) (b : n → α) :
    diagonal a ⊗ₖₜ[R] diagonal b = diagonal fun mn => a mn.1 ⊗ₜ b mn.2 :=
  kroneckerMap_diagonal_diagonal _ (zero_tmul _) (tmul_zero _) _ _
#align matrix.diagonal_kronecker_tmul_diagonal Matrix.diagonal_kronecker_tmul_diagonal

theorem kronecker_tmul_diagonal [DecidableEq n] (A : Matrix l m α) (b : n → α) :
    A ⊗ₖₜ[R] diagonal b = blockDiagonal fun i => A.map fun a => a ⊗ₜ[R] b i :=
  kroneckerMap_diagonal_right _ (tmul_zero _) _ _
#align matrix.kronecker_tmul_diagonal Matrix.kronecker_tmul_diagonal

theorem diagonal_kronecker_tmul [DecidableEq l] (a : l → α) (B : Matrix m n α) :
    diagonal a ⊗ₖₜ[R] B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
        (blockDiagonal fun i => B.map fun b => a i ⊗ₜ[R] b) :=
  kroneckerMap_diagonal_left _ (zero_tmul _) _ _
#align matrix.diagonal_kronecker_tmul Matrix.diagonal_kronecker_tmul

@[simp]
theorem kronecker_tmul_assoc (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r γ) :
    reindex (Equiv.prodAssoc l n q) (Equiv.prodAssoc m p r)
        (((A ⊗ₖₜ[R] B) ⊗ₖₜ[R] C).map (TensorProduct.assoc _ _ _ _)) =
      A ⊗ₖₜ[R] B ⊗ₖₜ[R] C :=
  ext fun i j => assoc_tmul _ _ _
#align matrix.kronecker_tmul_assoc Matrix.kronecker_tmul_assoc

theorem trace_kronecker_tmul [Fintype m] [Fintype n] (A : Matrix m m α) (B : Matrix n n β) :
    trace (A ⊗ₖₜ[R] B) = trace A ⊗ₜ[R] trace B :=
  trace_kroneckerMapBilinear (TensorProduct.mk R α β) _ _
#align matrix.trace_kronecker_tmul Matrix.trace_kronecker_tmul

end Module

section Algebra

open Kronecker

open Algebra.TensorProduct

section Semiring

variable [CommSemiring R] [Semiring α] [Semiring β] [Algebra R α] [Algebra R β]

@[simp]
theorem one_kronecker_tmul_one [DecidableEq m] [DecidableEq n] :
    (1 : Matrix m m α) ⊗ₖₜ[R] (1 : Matrix n n α) = 1 :=
  kroneckerMap_one_one _ (zero_tmul _) (tmul_zero _) rfl
#align matrix.one_kronecker_tmul_one Matrix.one_kronecker_tmul_one

theorem mul_kronecker_tmul_mul [Fintype m] [Fintype m'] (A : Matrix l m α) (B : Matrix m n α)
    (A' : Matrix l' m' β) (B' : Matrix m' n' β) : (A ⬝ B) ⊗ₖₜ[R] (A' ⬝ B') = A ⊗ₖₜ A' ⬝ B ⊗ₖₜ B' :=
  kroneckerMapBilinear_mul_mul (TensorProduct.mk R α β) tmul_mul_tmul A B A' B'
#align matrix.mul_kronecker_tmul_mul Matrix.mul_kronecker_tmul_mul

end Semiring

section CommRing

variable [CommRing R] [CommRing α] [CommRing β] [Algebra R α] [Algebra R β]

theorem det_kronecker_tmul [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m α) (B : Matrix n n β) :
    det (A ⊗ₖₜ[R] B) = (det A ^ Fintype.card n) ⊗ₜ[R] (det B ^ Fintype.card m) :=
  by
  refine' (det_kronecker_map_bilinear (TensorProduct.mk R α β) tmul_mul_tmul _ _).trans _
  simp (config := { eta := false }) only [mk_apply, ← include_left_apply, ← include_right_apply]
  simp only [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  simp only [include_left_apply, include_right_apply, tmul_pow, tmul_mul_tmul, one_pow,
    _root_.mul_one, _root_.one_mul]
#align matrix.det_kronecker_tmul Matrix.det_kronecker_tmul

end CommRing

end Algebra

-- insert lemmas specific to `kronecker_tmul` below this line
end KroneckerTmul

end Matrix

