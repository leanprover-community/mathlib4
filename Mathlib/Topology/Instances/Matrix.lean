/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Eric Wieser
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Star
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Topological properties of matrices

This file is a place to collect topological results about matrices.

## Main definitions:

* `Matrix.topologicalRing`: square matrices form a topological ring

## Main results

* Sets of matrices:
  * `IsOpen.matrix`: the set of finite matrices with entries in an open set
    is itself an open set.
  * `IsCompact.matrix`: the set of matrices with entries in a compact set
    is itself a compact set.
* Continuity:
  * `Continuous.matrix_det`: the determinant is continuous over a topological ring.
  * `Continuous.matrix_adjugate`: the adjugate is continuous over a topological ring.
* Infinite sums
  * `Matrix.transpose_tsum`: transpose commutes with infinite sums
  * `Matrix.diagonal_tsum`: diagonal commutes with infinite sums
  * `Matrix.blockDiagonal_tsum`: block diagonal commutes with infinite sums
  * `Matrix.blockDiagonal'_tsum`: non-uniform block diagonal commutes with infinite sums
-/


open Matrix

variable {X α l m n p S R : Type*} {m' n' : l → Type*}

instance [TopologicalSpace R] : TopologicalSpace (Matrix m n R) :=
  Pi.topologicalSpace

instance [TopologicalSpace R] [T2Space R] : T2Space (Matrix m n R) :=
  Pi.t2Space

/-- The topology on finite matrices over a discrete space is discrete. -/
instance [TopologicalSpace R] [Finite m] [Finite n] [DiscreteTopology R] :
    DiscreteTopology (Matrix m n R) :=
  Pi.discreteTopology

section Set

theorem IsOpen.matrix [Finite m] [Finite n]
    [TopologicalSpace R] {S : Set R} (hS : IsOpen S) :
    IsOpen (S.matrix : Set (Matrix m n R)) :=
  Set.matrix_eq_pi ▸
    (isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => hS).preimage continuous_id

theorem IsCompact.matrix [TopologicalSpace R] {S : Set R} (hS : IsCompact S) :
    IsCompact (S.matrix : Set (Matrix m n R)) :=
  isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hS

end Set

/-! ### Lemmas about continuity of operations -/

section Continuity

variable [TopologicalSpace X] [TopologicalSpace R]

instance [SMul α R] [ContinuousConstSMul α R] : ContinuousConstSMul α (Matrix m n R) :=
  inferInstanceAs (ContinuousConstSMul α (m → n → R))

instance [TopologicalSpace α] [SMul α R] [ContinuousSMul α R] : ContinuousSMul α (Matrix m n R) :=
  inferInstanceAs (ContinuousSMul α (m → n → R))

instance [Add R] [ContinuousAdd R] : ContinuousAdd (Matrix m n R) :=
  Pi.continuousAdd

instance [Neg R] [ContinuousNeg R] : ContinuousNeg (Matrix m n R) :=
  Pi.continuousNeg

instance [AddGroup R] [IsTopologicalAddGroup R] : IsTopologicalAddGroup (Matrix m n R) :=
  Pi.topologicalAddGroup

/-- To show a function into matrices is continuous it suffices to show the coefficients of the
resulting matrix are continuous -/
@[continuity]
theorem continuous_matrix [TopologicalSpace α] {f : α → Matrix m n R}
    (h : ∀ i j, Continuous fun a => f a i j) : Continuous f :=
  continuous_pi fun _ => continuous_pi fun _ => h _ _

theorem Continuous.matrix_elem {A : X → Matrix m n R} (hA : Continuous A) (i : m) (j : n) :
    Continuous fun x => A x i j :=
  (continuous_apply_apply i j).comp hA

@[continuity, fun_prop]
theorem Continuous.matrix_map [TopologicalSpace S] {A : X → Matrix m n S} {f : S → R}
    (hA : Continuous A) (hf : Continuous f) : Continuous fun x => (A x).map f :=
  continuous_matrix fun _ _ => hf.comp <| hA.matrix_elem _ _

@[continuity, fun_prop]
theorem Continuous.matrix_transpose {A : X → Matrix m n R} (hA : Continuous A) :
    Continuous fun x => (A x)ᵀ :=
  continuous_matrix fun i j => hA.matrix_elem j i

@[continuity, fun_prop]
theorem Continuous.matrix_conjTranspose [Star R] [ContinuousStar R] {A : X → Matrix m n R}
    (hA : Continuous A) : Continuous fun x => (A x)ᴴ :=
  hA.matrix_transpose.matrix_map continuous_star

instance [Star R] [ContinuousStar R] : ContinuousStar (Matrix m m R) :=
  ⟨continuous_id.matrix_conjTranspose⟩

@[continuity, fun_prop]
theorem Continuous.matrix_replicateCol {ι : Type*} {A : X → n → R} (hA : Continuous A) :
    Continuous fun x => replicateCol ι (A x) :=
  continuous_matrix fun i _ => (continuous_apply i).comp hA

@[continuity, fun_prop]
theorem Continuous.matrix_replicateRow {ι : Type*} {A : X → n → R} (hA : Continuous A) :
    Continuous fun x => replicateRow ι (A x) :=
  continuous_matrix fun _ _ => (continuous_apply _).comp hA

@[continuity, fun_prop]
theorem Continuous.matrix_diagonal [Zero R] [DecidableEq n] {A : X → n → R} (hA : Continuous A) :
    Continuous fun x => diagonal (A x) :=
  continuous_matrix fun i _ => ((continuous_apply i).comp hA).if_const _ continuous_zero

@[continuity, fun_prop]
protected theorem Continuous.dotProduct [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    [ContinuousMul R] {A : X → n → R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x ⬝ᵥ B x := by
  dsimp only [dotProduct]
  fun_prop

@[deprecated (since := "2025-05-09")]
alias Continuous.matrix_dotProduct := Continuous.dotProduct

/-- For square matrices the usual `continuous_mul` can be used. -/
@[continuity, fun_prop]
theorem Continuous.matrix_mul [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    [ContinuousMul R] {A : X → Matrix m n R} {B : X → Matrix n p R} (hA : Continuous A)
    (hB : Continuous B) : Continuous fun x => A x * B x :=
  continuous_matrix fun _ _ =>
    continuous_finset_sum _ fun _ _ => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)

instance [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R] [ContinuousMul R] :
    ContinuousMul (Matrix n n R) :=
  ⟨continuous_fst.matrix_mul continuous_snd⟩

instance [Fintype n] [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring (Matrix n n R) where

instance Matrix.topologicalRing [Fintype n] [NonUnitalNonAssocRing R] [IsTopologicalRing R] :
    IsTopologicalRing (Matrix n n R) where

@[continuity, fun_prop]
theorem Continuous.matrix_vecMulVec [Mul R] [ContinuousMul R] {A : X → m → R} {B : X → n → R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => vecMulVec (A x) (B x) :=
  continuous_matrix fun _ _ => ((continuous_apply _).comp hA).mul ((continuous_apply _).comp hB)

@[continuity, fun_prop]
theorem Continuous.matrix_mulVec [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    [Fintype n] {A : X → Matrix m n R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x *ᵥ B x :=
  continuous_pi fun i => ((continuous_apply i).comp hA).dotProduct hB

@[continuity, fun_prop]
theorem Continuous.matrix_vecMul [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    [Fintype m] {A : X → m → R} {B : X → Matrix m n R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x ᵥ* B x :=
  continuous_pi fun _i => hA.dotProduct <| continuous_pi fun _j => hB.matrix_elem _ _

@[continuity, fun_prop]
theorem Continuous.matrix_submatrix {A : X → Matrix l n R} (hA : Continuous A) (e₁ : m → l)
    (e₂ : p → n) : Continuous fun x => (A x).submatrix e₁ e₂ :=
  continuous_matrix fun _i _j => hA.matrix_elem _ _

@[continuity, fun_prop]
theorem Continuous.matrix_reindex {A : X → Matrix l n R} (hA : Continuous A) (e₁ : l ≃ m)
    (e₂ : n ≃ p) : Continuous fun x => reindex e₁ e₂ (A x) :=
  hA.matrix_submatrix _ _

@[continuity, fun_prop]
theorem Continuous.matrix_diag {A : X → Matrix n n R} (hA : Continuous A) :
    Continuous fun x => Matrix.diag (A x) :=
  continuous_pi fun _ => hA.matrix_elem _ _

-- note this doesn't elaborate well from the above
theorem continuous_matrix_diag : Continuous (Matrix.diag : Matrix n n R → n → R) :=
  show Continuous fun x : Matrix n n R => Matrix.diag x from continuous_id.matrix_diag

@[continuity, fun_prop]
theorem Continuous.matrix_trace [Fintype n] [AddCommMonoid R] [ContinuousAdd R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => trace (A x) :=
  continuous_finset_sum _ fun _ _ => hA.matrix_elem _ _

@[continuity, fun_prop]
theorem Continuous.matrix_det [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => (A x).det := by
  simp_rw [Matrix.det_apply]
  refine continuous_finset_sum _ fun l _ => Continuous.const_smul ?_ _
  exact continuous_finset_prod _ fun l _ => hA.matrix_elem _ _

@[continuity, fun_prop]
theorem Continuous.matrix_updateCol [DecidableEq n] (i : n) {A : X → Matrix m n R}
    {B : X → m → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x).updateCol i (B x) :=
  continuous_matrix fun _j k =>
    (continuous_apply k).comp <|
      ((continuous_apply _).comp hA).update i ((continuous_apply _).comp hB)

@[continuity, fun_prop]
theorem Continuous.matrix_updateRow [DecidableEq m] (i : m) {A : X → Matrix m n R} {B : X → n → R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => (A x).updateRow i (B x) :=
  hA.update i hB

@[continuity, fun_prop]
theorem Continuous.matrix_cramer [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {A : X → Matrix n n R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => cramer (A x) (B x) :=
  continuous_pi fun _ => (hA.matrix_updateCol _ hB).matrix_det

@[continuity, fun_prop]
theorem Continuous.matrix_adjugate [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => (A x).adjugate :=
  continuous_matrix fun _j k =>
    (hA.matrix_transpose.matrix_updateCol k continuous_const).matrix_det

/-- When `Ring.inverse` is continuous at the determinant (such as in a `NormedRing`, or a
topological field), so is `Matrix.inv`. -/
theorem continuousAt_matrix_inv [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    (A : Matrix n n R) (h : ContinuousAt Ring.inverse A.det) : ContinuousAt Inv.inv A :=
  (h.comp continuous_id.matrix_det.continuousAt).smul continuous_id.matrix_adjugate.continuousAt

namespace Topology

variable {m n R S : Type*} [TopologicalSpace R] [TopologicalSpace S] {f : R → S}

lemma IsInducing.matrix_map (hf : IsInducing f) :
    IsInducing (map · f : Matrix m n R → Matrix m n S) :=
  IsInducing.piMap fun _ : m ↦ (IsInducing.piMap fun _ : n ↦ hf)

lemma IsEmbedding.matrix_map (hf : IsEmbedding f) :
    IsEmbedding (map · f : Matrix m n R → Matrix m n S) :=
  IsEmbedding.piMap fun _ : m ↦ (IsEmbedding.piMap fun _ : n ↦ hf)

lemma IsClosedEmbedding.matrix_map (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (map · f : Matrix m n R → Matrix m n S) :=
  IsClosedEmbedding.piMap fun _ : m ↦ (IsClosedEmbedding.piMap fun _ : n ↦ hf)

lemma IsOpenEmbedding.matrix_map [Finite m] [Finite n] (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (map · f : Matrix m n R → Matrix m n S) :=
  IsOpenEmbedding.piMap fun _ : m ↦ (IsOpenEmbedding.piMap fun _ : n ↦ hf)

end Topology

-- lemmas about functions in `Data/Matrix/Block.lean`
section BlockMatrices

@[continuity, fun_prop]
theorem Continuous.matrix_fromBlocks {A : X → Matrix n l R} {B : X → Matrix n m R}
    {C : X → Matrix p l R} {D : X → Matrix p m R} (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hD : Continuous D) :
    Continuous fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x) :=
  continuous_matrix <| by
    rintro (i | i) (j | j) <;> refine Continuous.matrix_elem ?_ i j <;> assumption

@[continuity, fun_prop]
theorem Continuous.matrix_blockDiagonal [Zero R] [DecidableEq p] {A : X → p → Matrix m n R}
    (hA : Continuous A) : Continuous fun x => blockDiagonal (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, _j₂⟩ =>
    (((continuous_apply i₂).comp hA).matrix_elem i₁ j₁).if_const _ continuous_zero

@[continuity, fun_prop]
theorem Continuous.matrix_blockDiag {A : X → Matrix (m × p) (n × p) R} (hA : Continuous A) :
    Continuous fun x => blockDiag (A x) :=
  continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _

@[continuity, fun_prop]
theorem Continuous.matrix_blockDiagonal' [Zero R] [DecidableEq l]
    {A : X → ∀ i, Matrix (m' i) (n' i) R} (hA : Continuous A) :
    Continuous fun x => blockDiagonal' (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
    dsimp only [blockDiagonal'_apply']
    split_ifs with h
    · subst h
      exact ((continuous_apply i₁).comp hA).matrix_elem i₂ j₂
    · exact continuous_const

@[continuity, fun_prop]
theorem Continuous.matrix_blockDiag'
    {A : X → Matrix (Σ i, m' i) (Σ i, n' i) R} (hA : Continuous A) :
    Continuous fun x => blockDiag' (A x) :=
  continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _

end BlockMatrices

end Continuity

/-! ### Lemmas about infinite sums -/


section tsum

variable [AddCommMonoid R] [TopologicalSpace R] {L : SummationFilter X}

theorem HasSum.matrix_transpose {f : X → Matrix m n R} {a : Matrix m n R} (hf : HasSum f a L) :
    HasSum (fun x => (f x)ᵀ) aᵀ L :=
  (hf.map (Matrix.transposeAddEquiv m n R) continuous_id.matrix_transpose :)

theorem Summable.matrix_transpose {f : X → Matrix m n R} (hf : Summable f L) :
    Summable (fun x => (f x)ᵀ) L :=
  hf.hasSum.matrix_transpose.summable

@[simp]
theorem summable_matrix_transpose {f : X → Matrix m n R} :
    (Summable (fun x => (f x)ᵀ) L) ↔ Summable f L :=
  Summable.map_iff_of_equiv (Matrix.transposeAddEquiv m n R)
    continuous_id.matrix_transpose continuous_id.matrix_transpose

theorem Matrix.transpose_tsum [T2Space R] {f : X → Matrix m n R} :
    (∑'[L] x, f x)ᵀ = ∑'[L] x, (f x)ᵀ :=
  Function.LeftInverse.map_tsum f (g := transposeAddEquiv m n R) continuous_id.matrix_transpose
    continuous_id.matrix_transpose transpose_transpose

theorem HasSum.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R}
    {a : Matrix m n R} (hf : HasSum f a L) : HasSum (fun x => (f x)ᴴ) aᴴ L :=
  (hf.map (Matrix.conjTransposeAddEquiv m n R) continuous_id.matrix_conjTranspose :)

theorem Summable.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R}
    (hf : Summable f L) : Summable (fun x => (f x)ᴴ) L :=
  hf.hasSum.matrix_conjTranspose.summable

@[simp]
theorem summable_matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R} :
    (Summable (fun x => (f x)ᴴ) L) ↔ Summable f L :=
  Summable.map_iff_of_equiv (Matrix.conjTransposeAddEquiv m n R)
    continuous_id.matrix_conjTranspose continuous_id.matrix_conjTranspose

theorem Matrix.conjTranspose_tsum [StarAddMonoid R] [ContinuousStar R] [T2Space R]
    {f : X → Matrix m n R} : (∑'[L] x, f x)ᴴ = ∑'[L] x, (f x)ᴴ :=
  Function.LeftInverse.map_tsum f (g := conjTransposeAddEquiv m n R)
    continuous_id.matrix_conjTranspose continuous_id.matrix_conjTranspose
    conjTranspose_conjTranspose

theorem HasSum.matrix_diagonal [DecidableEq n] {f : X → n → R} {a : n → R} (hf : HasSum f a L) :
    HasSum (fun x => diagonal (f x)) (diagonal a) L :=
  hf.map (diagonalAddMonoidHom n R) continuous_id.matrix_diagonal

theorem Summable.matrix_diagonal [DecidableEq n] {f : X → n → R} (hf : Summable f L) :
    Summable (fun x => diagonal (f x)) L :=
  hf.hasSum.matrix_diagonal.summable

@[simp]
theorem summable_matrix_diagonal [DecidableEq n] {f : X → n → R} :
    (Summable (fun x => diagonal (f x)) L) ↔ Summable f L :=
  Summable.map_iff_of_leftInverse (Matrix.diagonalAddMonoidHom n R) (Matrix.diagAddMonoidHom n R)
    continuous_id.matrix_diagonal continuous_matrix_diag fun A => diag_diagonal A

theorem Matrix.diagonal_tsum [DecidableEq n] [T2Space R] {f : X → n → R} :
    diagonal (∑'[L] x, f x) = ∑'[L] x, diagonal (f x) :=
  Function.LeftInverse.map_tsum f (g := diagonalAddMonoidHom n R)
    continuous_id.matrix_diagonal continuous_matrix_diag diag_diagonal

theorem HasSum.matrix_diag {f : X → Matrix n n R} {a : Matrix n n R} (hf : HasSum f a L) :
    HasSum (fun x => diag (f x)) (diag a) L :=
  hf.map (diagAddMonoidHom n R) continuous_matrix_diag

theorem Summable.matrix_diag {f : X → Matrix n n R} (hf : Summable f L) :
    Summable (fun x => diag (f x)) L :=
  hf.hasSum.matrix_diag.summable

section BlockMatrices

theorem HasSum.matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R}
    {a : p → Matrix m n R} (hf : HasSum f a L) :
    HasSum (fun x => blockDiagonal (f x)) (blockDiagonal a) L :=
  hf.map (blockDiagonalAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal

theorem Summable.matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R}
    (hf : Summable f L) : Summable (fun x => blockDiagonal (f x)) L :=
  hf.hasSum.matrix_blockDiagonal.summable

theorem summable_matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R} :
    (Summable (fun x => blockDiagonal (f x)) L) ↔ Summable f L :=
  Summable.map_iff_of_leftInverse (blockDiagonalAddMonoidHom m n p R)
    (blockDiagAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal
    continuous_id.matrix_blockDiag fun A => blockDiag_blockDiagonal A

theorem Matrix.blockDiagonal_tsum [DecidableEq p] [T2Space R] {f : X → p → Matrix m n R} :
    blockDiagonal (∑'[L] x, f x) = ∑'[L] x, blockDiagonal (f x) :=
  Function.LeftInverse.map_tsum (g := blockDiagonalAddMonoidHom m n p R) f
    continuous_id.matrix_blockDiagonal continuous_id.matrix_blockDiag blockDiag_blockDiagonal

theorem HasSum.matrix_blockDiag {f : X → Matrix (m × p) (n × p) R} {a : Matrix (m × p) (n × p) R}
    (hf : HasSum f a L) : HasSum (fun x => blockDiag (f x)) (blockDiag a) L :=
  (hf.map (blockDiagAddMonoidHom m n p R) <| Continuous.matrix_blockDiag continuous_id :)

theorem Summable.matrix_blockDiag {f : X → Matrix (m × p) (n × p) R} (hf : Summable f L) :
    Summable (fun x => blockDiag (f x)) L :=
  hf.hasSum.matrix_blockDiag.summable

theorem HasSum.matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R}
    {a : ∀ i, Matrix (m' i) (n' i) R} (hf : HasSum f a L) :
    HasSum (fun x => blockDiagonal' (f x)) (blockDiagonal' a) L :=
  hf.map (blockDiagonal'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'

theorem Summable.matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R}
    (hf : Summable f L) : Summable (fun x => blockDiagonal' (f x)) L :=
  hf.hasSum.matrix_blockDiagonal'.summable

theorem summable_matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R} :
    (Summable (fun x => blockDiagonal' (f x)) L) ↔ Summable f L :=
  Summable.map_iff_of_leftInverse (blockDiagonal'AddMonoidHom m' n' R)
    (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'
    continuous_id.matrix_blockDiag' fun A => blockDiag'_blockDiagonal' A

theorem Matrix.blockDiagonal'_tsum [DecidableEq l] [T2Space R]
    {f : X → ∀ i, Matrix (m' i) (n' i) R} :
    blockDiagonal' (∑'[L] x, f x) = ∑'[L] x, blockDiagonal' (f x) :=
  Function.LeftInverse.map_tsum (g := blockDiagonal'AddMonoidHom m' n' R) f
    continuous_id.matrix_blockDiagonal' continuous_id.matrix_blockDiag' blockDiag'_blockDiagonal'

theorem HasSum.matrix_blockDiag' {f : X → Matrix (Σ i, m' i) (Σ i, n' i) R}
    {a : Matrix (Σ i, m' i) (Σ i, n' i) R} (hf : HasSum f a L) :
    HasSum (fun x => blockDiag' (f x)) (blockDiag' a) L :=
  hf.map (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiag'

theorem Summable.matrix_blockDiag' {f : X → Matrix (Σ i, m' i) (Σ i, n' i) R} (hf : Summable f L) :
    Summable (fun x => blockDiag' (f x)) L :=
  hf.hasSum.matrix_blockDiag'.summable

end BlockMatrices

end tsum

/-! ### Lemmas about matrix groups -/

section MatrixGroups

variable [Fintype n] [DecidableEq n]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

namespace Matrix.GeneralLinearGroup

/-- The determinant is continuous as a map from the general linear group to the units. -/
@[continuity, fun_prop] protected lemma continuous_det :
    Continuous (det : GL n R → Rˣ) := by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

@[continuity, fun_prop]
lemma continuous_upperRightHom {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (upperRightHom (R := R)) := by
  simp only [continuous_induced_rng, Function.comp_def, upperRightHom_apply,
    Units.embedProduct_apply, Units.inv_mk, continuous_prodMk, MulOpposite.unop_op]
  constructor <;>
  · refine continuous_matrix fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_neg, continuous_id']

end Matrix.GeneralLinearGroup

namespace Matrix.SpecialLinearGroup

local notation "SL" => SpecialLinearGroup

omit [IsTopologicalRing R] in
instance : TopologicalSpace (SpecialLinearGroup n R) :=
  instTopologicalSpaceSubtype

/-- If `R` is a commutative ring with the discrete topology, then `SL(n, R)` has the discrete
topology. -/
instance [DiscreteTopology R] : DiscreteTopology (SL n R) :=
  instDiscreteTopologySubtype

/-- The special linear group over a topological ring is a topological group. -/
instance topologicalGroup : IsTopologicalGroup (SL n R) where
  continuous_inv := by simpa [continuous_induced_rng] using continuous_induced_dom.matrix_adjugate
  continuous_mul := by simpa only [continuous_induced_rng] using
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)

section toGL -- results on the map from `SL` to `GL`

/-- The natural map from `SL n A` to `GL n A` is continuous. -/
lemma continuous_toGL : Continuous (toGL : SL n R → GL n R) := by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

/-- The natural map from `SL n A` to `GL n A` is inducing, i.e. the topology on
`SL n A` is the pullback of the topology from `GL n A`. -/
lemma isInducing_toGL : Topology.IsInducing (toGL : SL n R → GL n R) :=
  .of_comp continuous_toGL Units.continuous_val (Topology.IsInducing.induced _)

/-- The natural map from `SL n A` in `GL n A` is an embedding, i.e. it is an injection and
the topology on `SL n A` coincides with the subspace topology from `GL n A`. -/
lemma isEmbedding_toGL : Topology.IsEmbedding (toGL : SL n R → GL n R) :=
  ⟨isInducing_toGL, toGL_injective⟩

theorem range_toGL {A : Type*} [CommRing A] :
    Set.range (toGL : SL n A → GL n A) = GeneralLinearGroup.det ⁻¹' {1} := by
  ext x
  simpa [Units.ext_iff] using ⟨fun ⟨y, hy⟩ ↦ by simp [← hy], fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- The natural inclusion of `SL n A` in `GL n A` is a closed embedding. -/
lemma isClosedEmbedding_toGL [T0Space R] : Topology.IsClosedEmbedding (toGL : SL n R → GL n R) :=
  ⟨isEmbedding_toGL, by simpa [range_toGL] using isClosed_singleton.preimage <| by fun_prop⟩

end toGL

section mapGL

variable {n : Type*} [Fintype n] [DecidableEq n]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B]

lemma isInducing_mapGL (h : Topology.IsInducing (algebraMap A B)) :
    Topology.IsInducing (mapGL B : SL n A → GL n B) := by
  -- TODO: add `IsInducing.units_map` and deduce `IsInducing.generalLinearGroup_map`
  refine isInducing_toGL.comp ?_
  refine .of_comp ?_ continuous_induced_dom (h.matrix_map.comp (Topology.IsInducing.induced _))
  rw [continuous_induced_rng]
  exact continuous_subtype_val.matrix_map h.continuous

lemma isEmbedding_mapGL (h : Topology.IsEmbedding (algebraMap A B)) :
    Topology.IsEmbedding (mapGL B : SL n A → GL n B) :=
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).mpr h.2
  ⟨isInducing_mapGL h.isInducing, mapGL_injective⟩

end mapGL

end Matrix.SpecialLinearGroup

end MatrixGroups
