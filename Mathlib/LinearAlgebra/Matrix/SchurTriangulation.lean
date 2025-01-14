/-
Copyright (c) 2025 Gordon Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gordon Hsu
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
/-! # Schur triangulation

Schur triangulation is more commonly known as Schur decomposition or Schur triangularization, but
"triangulation" makes the API more readable. It states that a square matrix over an algebraically
closed field, e.g., `ℂ`, is unitarily similar to an upper triangular matrix.

## Main definitions

- `Matrix.schur_triangulation` : a matrix `A : Matrix n n 𝕜` with `𝕜` being algebraically closed can
be decomposed as `A = U * T * star U` where `U` is unitary and `T` is upper triangular.
- `Matrix.schurTriangulationUnitary` : the unitary matrix `U` as previously stated.
- `Matrix.schurTriangulation` : the upper triangular matrix `T` as previously stated.
- Some auxilary definitions are not meant to be used directly, but
`LinearMap.SchurTriangulationAux.of` contains the main algorithm for the triangulation procedure.

-/

section

variable {m n : ℕ}

/-- `subNat' i h` subtracts `m` from `i`. This is an alternative form of `Fin.subNat`. -/
@[inline] def Fin.subNat' (i : Fin (m + n)) (h : ¬ i < m) : Fin n :=
  subNat m (Fin.cast (m.add_comm n) i) (Nat.ge_of_not_lt h)

namespace Equiv

/-- The composition of `finSumFinEquiv` and `Equiv.sumEquivSigmalCond` used by
`LinearMap.SchurTriangulationAux.of`. -/
def finAddEquivSigmaCond : Fin (m + n) ≃ Σ b, cond b (Fin m) (Fin n) :=
  finSumFinEquiv.symm.trans (sumEquivSigmalCond (Fin m) (Fin n))

variable {i : Fin (m + n)}

lemma finAddEquivSigmaCond_true (h : i < m) : finAddEquivSigmaCond i = ⟨true, i, h⟩ :=
  congrArg (sumEquivSigmalCond (Fin m) (Fin n)) (finSumFinEquiv_symm_apply_castAdd ⟨i, h⟩)

lemma finAddEquivSigmaCond_false (h : ¬ i < m) : finAddEquivSigmaCond i = ⟨false, i.subNat' h⟩ :=
  let j : Fin n := i.subNat' h
  calc finAddEquivSigmaCond i
    _ = finAddEquivSigmaCond (Fin.natAdd m j) :=
      suffices m + (i - m) = i from congrArg _ (Fin.ext this.symm)
      Nat.add_sub_of_le (Nat.le_of_not_gt h)
    _ = ⟨false, i.subNat' h⟩ :=
      congrArg (sumEquivSigmalCond (Fin m) (Fin n)) (finSumFinEquiv_symm_apply_natAdd j)

end Equiv

end

variable {m n : Type _}

/-- The type family parameterized by `Bool` is finite if each type variant is finite. -/
instance [M : Fintype m] [N : Fintype n] (b : Bool) : Fintype (cond b m n) := b.rec N M

/-- The type family parameterized by `Bool` has decidable equality if each type variant is
decidable. -/
instance [DecidableEq m] [DecidableEq n] : DecidableEq (Σ b, cond b m n)
  | ⟨true, _⟩, ⟨false, _⟩
  | ⟨false, _⟩, ⟨true, _⟩ => isFalse nofun
  | ⟨false, i⟩, ⟨false, j⟩
  | ⟨true, i⟩, ⟨true, j⟩ =>
    if h : i = j then isTrue (Sigma.eq rfl h) else isFalse fun | rfl => h rfl

namespace LinearMap

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section

variable [FiniteDimensional 𝕜 E] [Fintype n] [DecidableEq n]

lemma toMatrixOrthonormal_apply_apply (b : OrthonormalBasis n 𝕜 E) (f : Module.End 𝕜 E)
    (i j : n) :
    toMatrixOrthonormal b f i j = ⟪b i, f (b j)⟫_𝕜 :=
  calc
    _ = b.repr (f (b j)) i := f.toMatrix_apply ..
    _ = ⟪b i, f (b j)⟫_𝕜 := b.repr_apply_apply ..

lemma toMatrixOrthonormal_reindex [Fintype m] [DecidableEq m]
    (b : OrthonormalBasis m 𝕜 E) (e : m ≃ n) (f : Module.End 𝕜 E) :
    toMatrixOrthonormal (b.reindex e) f = Matrix.reindex e e (toMatrixOrthonormal b f) :=
  Matrix.ext fun i j =>
    calc toMatrixOrthonormal (b.reindex e) f i j
      _ = (b.reindex e).repr (f (b.reindex e j)) i := f.toMatrix_apply ..
      _ = b.repr (f (b (e.symm j))) (e.symm i) := by simp
      _ = toMatrixOrthonormal b f (e.symm i) (e.symm j) := Eq.symm (f.toMatrix_apply ..)

end

/-- **Don't use this definition directly.** Instead, use `Matrix.schurTriangulationBasis`,
`Matrix.schurTriangulationUnitary`, and `Matrix.schurTriangulation`. See also
`LinearMap.SchurTriangulationAux.of` and `Matrix.schurTriangulationAux`. -/
structure SchurTriangulationAux (f : Module.End 𝕜 E) where
  /-- The dimension of the inner product space `E`. -/
  dim : ℕ
  hdim : Module.finrank 𝕜 E = dim
  /-- An orthonormal basis of `E` that induces an upper triangular form for `f`. -/
  basis : OrthonormalBasis (Fin dim) 𝕜 E
  upperTriangular : (toMatrix basis.toBasis basis.toBasis f).BlockTriangular _root_.id

end

/-! ## Schur's recursive triangulation procedure

Given a linear endomorphism `f` on a non-trivial finite-dimensional vector space `E` over an
algebraically closed field `𝕜`, one can always pick an eigenvalue `μ` of `f` whose corresponding
eigenspace `V` is non-trivial. Given that `E` is also an inner product space, let `bV` and `bW` be
othonormal bases for `V` and `Vᗮ` respectively. Then, the collection of vectors in `bV` and `bW`
forms an othornomal basis `bE` for `E`, as the direct sum of `V` and `Vᗮ` is an internal
decomposition of `E`. The matrix representation of `f` with respect to `bE` satisfies
$$
\sideset{_\mathrm{bE}}{_\mathrm{bE}}{[f]} =
\begin{bmatrix}
  \sideset{_\mathrm{bV}}{_\mathrm{bV}}{[f]} &
  \sideset{_\mathrm{bW}}{_\mathrm{bV}}{[f]} \\
  \sideset{_\mathrm{bV}}{_\mathrm{bW}}{[f]} &
  \sideset{_\mathrm{bW}}{_\mathrm{bW}}{[f]}
\end{bmatrix} =
\begin{bmatrix} \mu I & □ \\ 0 & \sideset{_\mathrm{bW}}{_\mathrm{bW}}{[f]} \end{bmatrix},
$$
which is upper triangular as long as $\sideset{_\mathrm{bW}}{_\mathrm{bW}}{[f]}$ is. Finally, one
observes that the recursion from $\sideset{_\mathrm{bE}}{_\mathrm{bE}}{[f]}$ to
$\sideset{_\mathrm{bW}}{_\mathrm{bW}}{[f]}$ is well-founded, as the dimension of `bW` is smaller
than that of `bE` because `bV` is non-trivial.

However, in order to leverage `DirectSum.IsInternal.collectedOrthonormalBasis`, the type
`Σ b, cond b (Fin m) (Fin n)` has to be used instead of the more natural `Fin m ⊕ Fin n` while their
equivalence is propositionally established by `Equiv.sumEquivSigmalCond`.

-/

variable [IsAlgClosed 𝕜]

/-- **Don't use this definition directly.** This is the key algorithm behind
`Matrix.schur_triangulation`. -/
protected noncomputable def SchurTriangulationAux.of {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (f : Module.End 𝕜 E) :
    SchurTriangulationAux f :=
  haveI : Decidable (Nontrivial E) := Classical.propDecidable _
  if hE : Nontrivial E then
    let μ : f.Eigenvalues := default
    let V : Submodule 𝕜 E := f.eigenspace μ
    let W : Submodule 𝕜 E := Vᗮ
    let m := Module.finrank 𝕜 V
    have hdim : m + Module.finrank 𝕜 W = Module.finrank 𝕜 E := V.finrank_add_finrank_orthogonal
    let g : Module.End 𝕜 W := orthogonalProjection W ∘ₗ f.domRestrict W
    let ⟨n, hn, bW, hg⟩ := SchurTriangulationAux.of g

    have bV : OrthonormalBasis (Fin m) 𝕜 V := stdOrthonormalBasis 𝕜 V
    have hV := V.orthogonalFamily_self
    have int : DirectSum.IsInternal (cond · V W) :=
      suffices ⨆ b, cond b V W = ⊤ from (hV.decomposition this).isInternal _
      (sup_eq_iSup V W).symm.trans Submodule.sup_orthogonal_of_completeSpace
    let B (b : Bool) : OrthonormalBasis (cond b (Fin m) (Fin n)) 𝕜 ↥(cond b V W) := b.rec bW bV
    let bE : OrthonormalBasis (Σ b, cond b (Fin m) (Fin n)) 𝕜 E :=
      int.collectedOrthonormalBasis hV B
    let e := Equiv.finAddEquivSigmaCond
    let basis := bE.reindex e.symm
    {
      basis
      dim := m + n
      hdim := hn ▸ hdim.symm
      upperTriangular := fun i j (hji : j < i) => show toMatrixOrthonormal basis f i j = 0 from
        have hB : ∀ s, bE s = B s.1 s.2
          | ⟨true, i⟩ => show bE ⟨true, i⟩ = bV i from
            show (int.collectedBasis fun b => (B b).toBasis).toOrthonormalBasis _ ⟨true, i⟩ = bV i
            by simp ; rfl
          | ⟨false, j⟩ => show bE ⟨false, j⟩ = bW j from
            show (int.collectedBasis fun b => (B b).toBasis).toOrthonormalBasis _ ⟨false, j⟩ = bW j
            by simp ; rfl
        have hf {bi i' bj j'} (hi : e i = ⟨bi, i'⟩) (hj : e j = ⟨bj, j'⟩) :=
          calc toMatrixOrthonormal basis f i j
            _ = toMatrixOrthonormal bE f (e i) (e j) := by
              rw [f.toMatrixOrthonormal_reindex]
              rfl
            _ = ⟪bE (e i), f (bE (e j))⟫_𝕜 := f.toMatrixOrthonormal_apply_apply ..
            _ = ⟪(B bi i' : E), f (B bj j')⟫_𝕜 := by rw [hB, hB, hi, hj]

        if hj : j < m then
          let j' : Fin m := ⟨j, hj⟩
          have hf' {bi i'} (hi : e i = ⟨bi, i'⟩) (h0 : ⟪(B bi i' : E), bV j'⟫_𝕜 = 0) :=
            calc toMatrixOrthonormal basis f i j
              _ = ⟪(B bi i' : E), f _⟫_𝕜 := hf hi (Equiv.finAddEquivSigmaCond_true hj)
              _ = ⟪_, f (bV j')⟫_𝕜 := rfl
              _ = 0 :=
                suffices f (bV j') = μ.val • bV j' by rw [this, inner_smul_right, h0, mul_zero]
                suffices f.HasEigenvector μ (bV j') from this.apply_eq_smul
                ⟨(bV j').property, fun h => bV.toBasis.ne_zero j' (Subtype.ext h)⟩

          if hi : i < m then
            let i' : Fin m := ⟨i, hi⟩
            suffices ⟪(bV i' : E), bV j'⟫_𝕜 = 0 from hf' (Equiv.finAddEquivSigmaCond_true hi) this
            bV.orthonormal.right (Fin.ne_of_gt hji)
          else
            let i' : Fin n := i.subNat' hi
            suffices ⟪(bW i' : E), bV j'⟫_𝕜 = 0 from hf' (Equiv.finAddEquivSigmaCond_false hi) this
            V.inner_left_of_mem_orthogonal (bV j').property (bW i').property
        else
          have hi (h : i < m) : False := hj (Nat.lt_trans hji h)
          let i' : Fin n := i.subNat' hi
          let j' : Fin n := j.subNat' hj
          calc toMatrixOrthonormal basis f i j
            _ = ⟪(bW i' : E), f (bW j')⟫_𝕜 :=
              hf (Equiv.finAddEquivSigmaCond_false hi) (Equiv.finAddEquivSigmaCond_false hj)
            _ = ⟪bW i', g (bW j')⟫_𝕜 := by simp [g]
            _ = toMatrixOrthonormal bW g i' j' := (g.toMatrixOrthonormal_apply_apply ..).symm
            _ = 0 := hg (Nat.sub_lt_sub_right (Nat.le_of_not_lt hj) hji)
    }
  else
    haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    {
      dim := 0
      hdim := Module.finrank_zero_of_subsingleton
      basis := (Basis.empty E).toOrthonormalBasis ⟨nofun, nofun⟩
      upperTriangular := nofun
    }
termination_by Module.finrank 𝕜 E
decreasing_by exact
  calc Module.finrank 𝕜 W
    _ < m + Module.finrank 𝕜 W :=
      suffices 0 < m from Nat.lt_add_of_pos_left this
      Submodule.one_le_finrank_iff.mpr μ.property
    _ = Module.finrank 𝕜 E := hdim

end LinearMap

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜]
/- IMPORTANT: existing `DecidableEq n` should take precedence over `LinearOrder.decidableEq`,
a.k.a., `instDecidableEq_mathlib`. -/
variable [Fintype n] [DecidableEq n] [LinearOrder n] (A : Matrix n n 𝕜)

/-- **Don't use this definition directly.** Instead, use `Matrix.schurTriangulationBasis`,
`Matrix.schurTriangulationUnitary`, and `Matrix.schurTriangulation` for which this is their
simultaneous definition. This is `LinearMap.SchurTriangulationAux` adapted for matrices in the
Euclidean space. -/
noncomputable def schurTriangulationAux :
    OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) × UpperTriangular n 𝕜 :=
  let f := toEuclideanLin A
  let ⟨d, hd, b, hut⟩ := LinearMap.SchurTriangulationAux.of f
  let e : Fin d ≃o n := Fintype.orderIsoFinOfCardEq n (finrank_euclideanSpace.symm.trans hd)
  let b' := b.reindex e
  let B := LinearMap.toMatrixOrthonormal b' f
  suffices B.IsUpperTriangular from ⟨b', B, this⟩
  fun i j (hji : j < i) =>
    calc LinearMap.toMatrixOrthonormal b' f i j
      _ = LinearMap.toMatrixOrthonormal b f (e.symm i) (e.symm j) := by
        rw [f.toMatrixOrthonormal_reindex]
        rfl
      _ = 0 := hut (e.symm.lt_iff_lt.mpr hji)

/-- The change of basis that induces the upper triangular form `A.schurTriangulation` of a matrix
`A` over an algebraically closed field. -/
noncomputable def schurTriangulationBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  A.schurTriangulationAux.1

/-- The unitary matrix that induces the upper triangular form `A.schurTriangulation` to which a
matrix `A` over an algebraically closed field is unitarily similar. -/
noncomputable def schurTriangulationUnitary : unitaryGroup n 𝕜 where
  val := (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix A.schurTriangulationBasis
  property := OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary ..

/-- The upper triangular form induced by `A.schurTriangulationUnitary` to which a matrix `A` over an
algebraically closed field is unitarily similar. -/
noncomputable def schurTriangulation : UpperTriangular n 𝕜 :=
  A.schurTriangulationAux.2

/-- **Schur triangulation**, **Schur decomposition** for matrices over an algebraically closed
field. In particular, a complex matrix can be converted to upper-triangular form by a change of
basis. In other words, any complex matrix is unitarily similar to an upper triangular matrix. -/
lemma schur_triangulation :
    A = A.schurTriangulationUnitary * A.schurTriangulation * star A.schurTriangulationUnitary :=
  let U := A.schurTriangulationUnitary
  have h : U * A.schurTriangulation.val = A * U :=
    let b := A.schurTriangulationBasis.toBasis
    let c := (EuclideanSpace.basisFun n 𝕜).toBasis
    calc c.toMatrix b * LinearMap.toMatrix b b (toEuclideanLin A)
      _ = LinearMap.toMatrix c c (toEuclideanLin A) * c.toMatrix b := by simp
      _ = LinearMap.toMatrix c c (toLin c c A) * U := rfl
      _ = A * U := by simp
  calc A
    _ = A * U * star U := by simp [mul_assoc]
    _ = U * A.schurTriangulation * star U := by rw [← h]

end Matrix
