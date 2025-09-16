/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Determinant of families of vectors

This file defines the determinant of an endomorphism, and of a family of vectors
with respect to some basis. For the determinant of a matrix, see the file
`LinearAlgebra.Matrix.Determinant`.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

* `Basis.det`: the determinant of a family of vectors with respect to a basis,
  as a multilinear map
* `LinearMap.det`: the determinant of an endomorphism `f : End R M` as a
  multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
  result is `1` instead)
* `LinearEquiv.det`: the determinant of an isomorphism `f : M ≃ₗ[R] M` as a
  multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
  result is `1` instead)

## Tags

basis, det, determinant
-/


noncomputable section

open Matrix Module LinearMap Submodule Set Function

universe u v w

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {M' : Type*} [AddCommGroup M'] [Module R M']
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable (e : Basis ι R M)

section Conjugate

variable {A : Type*} [CommRing A]
variable {m n : Type*}

/-- If `R^m` and `R^n` are linearly equivalent, then `m` and `n` are also equivalent. -/
def equivOfPiLEquivPi {R : Type*} [Finite m] [Finite n] [CommRing R] [Nontrivial R]
    (e : (m → R) ≃ₗ[R] n → R) : m ≃ n :=
  Basis.indexEquiv (Basis.ofEquivFun e.symm) (Pi.basisFun _ _)

namespace Matrix

variable [Fintype m] [Fintype n]

/-- If `M` and `M'` are each other's inverse matrices, they are square matrices up to
equivalence of types. -/
def indexEquivOfInv [Nontrivial A] [DecidableEq m] [DecidableEq n] {M : Matrix m n A}
    {M' : Matrix n m A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : m ≃ n :=
  equivOfPiLEquivPi (toLin'OfInv hMM' hM'M)

theorem det_comm [DecidableEq n] (M N : Matrix n n A) : det (M * N) = det (N * M) := by
  rw [det_mul, det_mul, mul_comm]

/-- If there exists a two-sided inverse `M'` for `M` (indexed differently),
then `det (N * M) = det (M * N)`. -/
theorem det_comm' [DecidableEq m] [DecidableEq n] {M : Matrix n m A} {N : Matrix m n A}
    {M' : Matrix m n A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : det (M * N) = det (N * M) := by
  nontriviality A
  -- Although `m` and `n` are different a priori, we will show they have the same cardinality.
  -- This turns the problem into one for square matrices, which is easy.
  let e := indexEquivOfInv hMM' hM'M
  rw [← det_submatrix_equiv_self e, ← submatrix_mul_equiv _ _ _ (Equiv.refl n) _, det_comm,
    submatrix_mul_equiv, Equiv.coe_refl, submatrix_id_id]

/-- If `M'` is a two-sided inverse for `M` (indexed differently), `det (M * N * M') = det N`.

See `Matrix.det_conj` and `Matrix.det_conj'` for the case when `M' = M⁻¹` or vice versa. -/
theorem det_conj_of_mul_eq_one [DecidableEq m] [DecidableEq n] {M : Matrix m n A}
    {M' : Matrix n m A} {N : Matrix n n A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) :
    det (M * N * M') = det N := by
  rw [← det_comm' hM'M hMM', ← Matrix.mul_assoc, hM'M, Matrix.one_mul]

end Matrix

end Conjugate

namespace LinearMap

/-! ### Determinant of a linear map -/


variable {A : Type*} [CommRing A] [Module A M]
variable {κ : Type*} [Fintype κ]

/-- The determinant of `LinearMap.toMatrix` does not depend on the choice of basis. -/
theorem det_toMatrix_eq_det_toMatrix [DecidableEq κ] (b : Basis ι A M) (c : Basis κ A M)
    (f : M →ₗ[A] M) : det (LinearMap.toMatrix b b f) = det (LinearMap.toMatrix c c f) := by
  rw [← linearMap_toMatrix_mul_basis_toMatrix c b c, ← basis_toMatrix_mul_linearMap_toMatrix b c b,
      Matrix.det_conj_of_mul_eq_one] <;>
    rw [Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]


/-- The determinant of an endomorphism given a basis.

See `LinearMap.det` for a version that populates the basis non-computably.

Although the `Trunc (Basis ι A M)` parameter makes it slightly more convenient to switch bases,
there is no good way to generalize over universe parameters, so we can't fully state in `detAux`'s
type that it does not depend on the choice of basis. Instead you can use the `detAux_def''` lemma,
or avoid mentioning a basis at all using `LinearMap.det`.
-/
irreducible_def detAux : Trunc (Basis ι A M) → (M →ₗ[A] M) →* A :=
  Trunc.lift
    (fun b : Basis ι A M => detMonoidHom.comp (toMatrixAlgEquiv b : (M →ₗ[A] M) →* Matrix ι ι A))
    fun b c => MonoidHom.ext <| det_toMatrix_eq_det_toMatrix b c

/-- Unfold lemma for `detAux`.

See also `detAux_def''` which allows you to vary the basis.
-/
theorem detAux_def' (b : Basis ι A M) (f : M →ₗ[A] M) :
    LinearMap.detAux (Trunc.mk b) f = Matrix.det (LinearMap.toMatrix b b f) := by
  rw [detAux]
  rfl

theorem detAux_def'' {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (tb : Trunc <| Basis ι A M)
    (b' : Basis ι' A M) (f : M →ₗ[A] M) :
    LinearMap.detAux tb f = Matrix.det (LinearMap.toMatrix b' b' f) := by
  induction tb using Trunc.induction_on with
  | h b => rw [detAux_def', det_toMatrix_eq_det_toMatrix b b']

@[simp]
theorem detAux_id (b : Trunc <| Basis ι A M) : LinearMap.detAux b LinearMap.id = 1 :=
  (LinearMap.detAux b).map_one

@[simp]
theorem detAux_comp (b : Trunc <| Basis ι A M) (f g : M →ₗ[A] M) :
    LinearMap.detAux b (f.comp g) = LinearMap.detAux b f * LinearMap.detAux b g :=
  (LinearMap.detAux b).map_mul f g

section

open scoped Classical in
-- Discourage the elaborator from unfolding `det` and producing a huge term by marking it
-- as irreducible.
/-- The determinant of an endomorphism independent of basis.

If there is no finite basis on `M`, the result is `1` instead.
-/
protected irreducible_def det : (M →ₗ[A] M) →* A :=
  if H : ∃ s : Finset M, Nonempty (Basis s A M) then LinearMap.detAux (Trunc.mk H.choose_spec.some)
  else 1

open scoped Classical in
theorem coe_det [DecidableEq M] :
    ⇑(LinearMap.det : (M →ₗ[A] M) →* A) =
      if H : ∃ s : Finset M, Nonempty (Basis s A M) then
        LinearMap.detAux (Trunc.mk H.choose_spec.some)
      else 1 := by
  ext
  rw [LinearMap.det_def]
  split_ifs
  · congr -- use the correct `DecidableEq` instance
  rfl

end

-- Auxiliary lemma, the `simp` normal form goes in the other direction
-- (using `LinearMap.det_toMatrix`)
theorem det_eq_det_toMatrix_of_finset [DecidableEq M] {s : Finset M} (b : Basis s A M)
    (f : M →ₗ[A] M) : LinearMap.det f = Matrix.det (LinearMap.toMatrix b b f) := by
  have : ∃ s : Finset M, Nonempty (Basis s A M) := ⟨s, ⟨b⟩⟩
  rw [LinearMap.coe_det, dif_pos this, detAux_def'' _ b]

@[simp]
theorem det_toMatrix (b : Basis ι A M) (f : M →ₗ[A] M) :
    Matrix.det (toMatrix b b f) = LinearMap.det f := by
  haveI := Classical.decEq M
  rw [det_eq_det_toMatrix_of_finset b.reindexFinsetRange,
    det_toMatrix_eq_det_toMatrix b b.reindexFinsetRange]

@[simp]
theorem det_toMatrix' {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → A) →ₗ[A] ι → A) :
    Matrix.det (LinearMap.toMatrix' f) = LinearMap.det f := by simp [← toMatrix_eq_toMatrix']

@[simp]
theorem det_toLin (b : Basis ι R M) (f : Matrix ι ι R) :
    LinearMap.det (Matrix.toLin b b f) = f.det := by
  rw [← LinearMap.det_toMatrix b, LinearMap.toMatrix_toLin]

@[simp]
theorem det_toLin' (f : Matrix ι ι R) : LinearMap.det (Matrix.toLin' f) = Matrix.det f := by
  simp only [← toLin_eq_toLin', det_toLin]

/-- To show `P (LinearMap.det f)` it suffices to consider `P (Matrix.det (toMatrix _ _ f))` and
`P 1`. -/
@[elab_as_elim]
theorem det_cases [DecidableEq M] {P : A → Prop} (f : M →ₗ[A] M)
    (hb : ∀ (s : Finset M) (b : Basis s A M), P (Matrix.det (toMatrix b b f))) (h1 : P 1) :
    P (LinearMap.det f) := by
  classical
  if H : ∃ s : Finset M, Nonempty (Basis s A M) then
    obtain ⟨s, ⟨b⟩⟩ := H
    rw [← det_toMatrix b]
    exact hb s b
  else
    rwa [LinearMap.det_def, dif_neg H]

@[simp]
theorem det_comp (f g : M →ₗ[A] M) :
    LinearMap.det (f.comp g) = LinearMap.det f * LinearMap.det g :=
  LinearMap.det.map_mul f g

@[simp]
theorem det_id : LinearMap.det (LinearMap.id : M →ₗ[A] M) = 1 :=
  LinearMap.det.map_one

/-- Multiplying a map by a scalar `c` multiplies its determinant by `c ^ dim M`. -/
@[simp]
theorem det_smul [Module.Free A M] (c : A) (f : M →ₗ[A] M) :
    LinearMap.det (c • f) = c ^ Module.finrank A M * LinearMap.det f := by
  nontriviality A
  by_cases H : ∃ s : Finset M, Nonempty (Basis s A M)
  · have : Module.Finite A M := by
      rcases H with ⟨s, ⟨hs⟩⟩
      exact Module.Finite.of_basis hs
    simp only [← det_toMatrix (Module.finBasis A M), LinearEquiv.map_smul,
      Fintype.card_fin, Matrix.det_smul]
  · classical
      have : Module.finrank A M = 0 := finrank_eq_zero_of_not_exists_basis H
      simp [coe_det, H, this]

theorem det_zero' {ι : Type*} [Finite ι] [Nonempty ι] (b : Basis ι A M) :
    LinearMap.det (0 : M →ₗ[A] M) = 0 := by
  haveI := Classical.decEq ι
  cases nonempty_fintype ι
  rwa [← det_toMatrix b, LinearEquiv.map_zero, det_zero]

/-- In a finite-dimensional vector space, the zero map has determinant `1` in dimension `0`,
and `0` otherwise. We give a formula that also works in infinite dimension, where we define
the determinant to be `1`. -/
@[simp]
theorem det_zero [Module.Free A M] :
    LinearMap.det (0 : M →ₗ[A] M) = (0 : A) ^ Module.finrank A M := by
  simp only [← zero_smul A (1 : M →ₗ[A] M), det_smul, mul_one, MonoidHom.map_one]

theorem det_eq_one_of_not_module_finite (h : ¬Module.Finite R M) (f : M →ₗ[R] M) : f.det = 1 := by
  rw [LinearMap.det, dif_neg, MonoidHom.one_apply]
  exact fun ⟨_, ⟨b⟩⟩ ↦ h (Module.Finite.of_basis b)

@[nontriviality]
theorem det_eq_one_of_subsingleton [Subsingleton M] (f : M →ₗ[R] M) :
    LinearMap.det (f : M →ₗ[R] M) = 1 := by
  have b : Basis (Fin 0) R M := Basis.empty M
  rw [← f.det_toMatrix b]
  exact Matrix.det_isEmpty

theorem det_eq_one_of_finrank_eq_zero {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M]
    [Module 𝕜 M] (h : Module.finrank 𝕜 M = 0) (f : M →ₗ[𝕜] M) :
    LinearMap.det (f : M →ₗ[𝕜] M) = 1 := by
  classical
    refine @LinearMap.det_cases M _ 𝕜 _ _ _ (fun t => t = 1) f ?_ rfl
    intro s b
    have : IsEmpty s := by
      rw [← Fintype.card_eq_zero_iff]
      exact (Module.finrank_eq_card_basis b).symm.trans h
    exact Matrix.det_isEmpty

/-- Conjugating a linear map by a linear equiv does not change its determinant. -/
@[simp]
theorem det_conj {N : Type*} [AddCommGroup N] [Module A N] (f : M →ₗ[A] M) (e : M ≃ₗ[A] N) :
    LinearMap.det ((e : M →ₗ[A] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[A] M)) = LinearMap.det f := by
  classical
    by_cases H : ∃ s : Finset M, Nonempty (Basis s A M)
    · rcases H with ⟨s, ⟨b⟩⟩
      rw [← det_toMatrix b f, ← det_toMatrix (b.map e), toMatrix_comp (b.map e) b (b.map e),
        toMatrix_comp (b.map e) b b, ← Matrix.mul_assoc, Matrix.det_conj_of_mul_eq_one]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.symm_trans_self, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.self_trans_symm, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
    · have H' : ¬∃ t : Finset N, Nonempty (Basis t A N) := by
        contrapose! H
        rcases H with ⟨s, ⟨b⟩⟩
        exact ⟨_, ⟨(b.map e.symm).reindexFinsetRange⟩⟩
      simp only [coe_det, H, H', MonoidHom.one_apply, dif_neg, not_false_eq_true]

/-- If a linear map is invertible, so is its determinant. -/
theorem isUnit_det {A : Type*} [CommRing A] [Module A M] (f : M →ₗ[A] M) (hf : IsUnit f) :
    IsUnit (LinearMap.det f) := IsUnit.map LinearMap.det hf

/-- If a linear map has determinant different from `1`, then the space is finite-dimensional. -/
theorem finiteDimensional_of_det_ne_one {𝕜 : Type*} [Field 𝕜] [Module 𝕜 M] (f : M →ₗ[𝕜] M)
    (hf : LinearMap.det f ≠ 1) : FiniteDimensional 𝕜 M := by
  by_cases H : ∃ s : Finset M, Nonempty (Basis s 𝕜 M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact FiniteDimensional.of_fintype_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

/-- If the determinant of a map vanishes, then the map is not onto. -/
theorem range_lt_top_of_det_eq_zero {𝕜 : Type*} [Field 𝕜] [Module 𝕜 M] {f : M →ₗ[𝕜] M}
    (hf : LinearMap.det f = 0) : LinearMap.range f < ⊤ := by
  have : FiniteDimensional 𝕜 M := by simp [f.finiteDimensional_of_det_ne_one, hf]
  contrapose hf
  simp only [lt_top_iff_ne_top, Classical.not_not, ← isUnit_iff_range_eq_top] at hf
  exact isUnit_iff_ne_zero.1 (f.isUnit_det hf)

/-- If the determinant of a map vanishes, then the map is not injective. -/
theorem bot_lt_ker_of_det_eq_zero {𝕜 : Type*} [Field 𝕜] [Module 𝕜 M] {f : M →ₗ[𝕜] M}
    (hf : LinearMap.det f = 0) : ⊥ < LinearMap.ker f := by
  have : FiniteDimensional 𝕜 M := by simp [f.finiteDimensional_of_det_ne_one, hf]
  contrapose hf
  simp only [bot_lt_iff_ne_bot, Classical.not_not, ← isUnit_iff_ker_eq_bot] at hf
  exact isUnit_iff_ne_zero.1 (f.isUnit_det hf)

/-- When the function is over the base ring, the determinant is the evaluation at `1`. -/
@[simp] lemma det_ring (f : R →ₗ[R] R) : f.det = f 1 := by
  simp [← det_toMatrix (Basis.singleton Unit R)]

lemma det_mulLeft (a : R) : (mulLeft R a).det = a := by simp
lemma det_mulRight (a : R) : (mulRight R a).det = a := by simp

theorem det_prodMap [Module.Free R M] [Module.Free R M'] [Module.Finite R M] [Module.Finite R M']
    (f : Module.End R M) (f' : Module.End R M') :
    (prodMap f f').det = f.det * f'.det := by
  let b := Module.Free.chooseBasis R M
  let b' := Module.Free.chooseBasis R M'
  rw [← det_toMatrix (b.prod b'), ← det_toMatrix b, ← det_toMatrix b', toMatrix_prodMap,
    det_fromBlocks_zero₂₁, det_toMatrix]

omit [DecidableEq ι] in
theorem det_pi [Module.Free R M] [Module.Finite R M] (f : ι → M →ₗ[R] M) :
    (LinearMap.pi (fun i ↦ (f i).comp (LinearMap.proj i))).det = ∏ i, (f i).det := by
  classical
  let b := Module.Free.chooseBasis R M
  let B := (Pi.basis (fun _ : ι ↦ b)).reindex <|
    (Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _)
  simp_rw [← LinearMap.det_toMatrix B, ← LinearMap.det_toMatrix b]
  have : ((LinearMap.toMatrix B B) (LinearMap.pi fun i ↦ f i ∘ₗ LinearMap.proj i)) =
      Matrix.blockDiagonal (fun i ↦ LinearMap.toMatrix b b (f i)) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    unfold B
    simp_rw [LinearMap.toMatrix_apply', Matrix.blockDiagonal_apply, Basis.coe_reindex,
      Function.comp_apply, Basis.repr_reindex_apply, Equiv.symm_trans_apply, Equiv.prodComm_symm,
      Equiv.prodComm_apply, Equiv.sigmaEquivProd_symm_apply, Prod.swap_prod_mk, Pi.basis_apply,
      Pi.basis_repr, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toMatrix_apply', LinearMap.coe_proj, Function.eval, Pi.single_apply]
    split_ifs with h
    · rw [h]
    · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [this, Matrix.det_blockDiagonal]

end LinearMap


namespace LinearEquiv

/-- On a `LinearEquiv`, the domain of `LinearMap.det` can be promoted to `Rˣ`. -/
protected def det : (M ≃ₗ[R] M) →* Rˣ :=
  (Units.map (LinearMap.det : (M →ₗ[R] M) →* R)).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).symm.toMonoidHom

@[simp]
theorem coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = LinearMap.det (f : M →ₗ[R] M) :=
  rfl

@[simp]
theorem coe_inv_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f)⁻¹ = LinearMap.det (f.symm : M →ₗ[R] M) :=
  rfl

@[simp]
theorem det_refl : LinearEquiv.det (LinearEquiv.refl R M) = 1 :=
  Units.ext <| LinearMap.det_id

@[simp]
theorem det_trans (f g : M ≃ₗ[R] M) :
    LinearEquiv.det (f.trans g) = LinearEquiv.det g * LinearEquiv.det f :=
  map_mul _ g f

@[simp]
theorem det_symm (f : M ≃ₗ[R] M) : LinearEquiv.det f.symm = LinearEquiv.det f⁻¹ :=
  map_inv _ f

/-- Conjugating a linear equiv by a linear equiv does not change its determinant. -/
@[simp]
theorem det_conj (f : M ≃ₗ[R] M) (e : M ≃ₗ[R] M') :
    LinearEquiv.det ((e.symm.trans f).trans e) = LinearEquiv.det f := by
  rw [← Units.val_inj, coe_det, coe_det, ← comp_coe, ← comp_coe, LinearMap.det_conj]

attribute [irreducible] LinearEquiv.det

end LinearEquiv

/-- The determinants of a `LinearEquiv` and its inverse multiply to 1. -/
@[simp]
theorem LinearEquiv.det_mul_det_symm {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M) :
    LinearMap.det (f : M →ₗ[A] M) * LinearMap.det (f.symm : M →ₗ[A] M) = 1 := by
  simp [← LinearMap.det_comp]

/-- The determinants of a `LinearEquiv` and its inverse multiply to 1. -/
@[simp]
theorem LinearEquiv.det_symm_mul_det {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M) :
    LinearMap.det (f.symm : M →ₗ[A] M) * LinearMap.det (f : M →ₗ[A] M) = 1 := by
  simp [← LinearMap.det_comp]

-- Cannot be stated using `LinearMap.det` because `f` is not an endomorphism.
theorem LinearEquiv.isUnit_det (f : M ≃ₗ[R] M') (v : Basis ι R M) (v' : Basis ι R M') :
    IsUnit (LinearMap.toMatrix v v' f).det := by
  apply isUnit_det_of_left_inverse
  simpa using (LinearMap.toMatrix_comp v v' v f.symm f).symm

/-- Specialization of `LinearEquiv.isUnit_det` -/
theorem LinearEquiv.isUnit_det' {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M) :
    IsUnit (LinearMap.det (f : M →ₗ[A] M)) :=
  isUnit_of_mul_eq_one _ _ f.det_mul_det_symm

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- The determinant of `f.symm` is the inverse of that of `f` when `f` is a linear equiv. -/
theorem LinearEquiv.det_coe_symm {𝕜 : Type*} [Field 𝕜] [Module 𝕜 M] (f : M ≃ₗ[𝕜] M) :
    LinearMap.det (f.symm : M →ₗ[𝕜] M) = (LinearMap.det (f : M →ₗ[𝕜] M))⁻¹ := by
  simp [field, IsUnit.ne_zero f.isUnit_det']

/-- Builds a linear equivalence from a linear map whose determinant in some bases is a unit. -/
@[simps]
def LinearEquiv.ofIsUnitDet {f : M →ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι R M'}
    (h : IsUnit (LinearMap.toMatrix v v' f).det) : M ≃ₗ[R] M' where
  toFun := f
  map_add' := f.map_add
  map_smul' := f.map_smul
  invFun := toLin v' v (toMatrix v v' f)⁻¹
  left_inv x :=
    calc toLin v' v (toMatrix v v' f)⁻¹ (f x)
      _ = toLin v v ((toMatrix v v' f)⁻¹ * toMatrix v v' f) x := by
        rw [toLin_mul v v' v, toLin_toMatrix, LinearMap.comp_apply]
      _ = x := by simp [h]
  right_inv x :=
    calc f (toLin v' v (toMatrix v v' f)⁻¹ x)
      _ = toLin v' v' (toMatrix v v' f * (toMatrix v v' f)⁻¹) x := by
        rw [toLin_mul v' v v', LinearMap.comp_apply, toLin_toMatrix v v']
      _ = x := by simp [h]

@[simp]
theorem LinearEquiv.coe_ofIsUnitDet {f : M →ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι R M'}
    (h : IsUnit (LinearMap.toMatrix v v' f).det) :
    (LinearEquiv.ofIsUnitDet h : M →ₗ[R] M') = f := by
  ext x
  rfl

/-- Builds a linear equivalence from a linear map on a finite-dimensional vector space whose
determinant is nonzero. -/
abbrev LinearMap.equivOfDetNeZero {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    [FiniteDimensional 𝕜 M] (f : M →ₗ[𝕜] M) (hf : LinearMap.det f ≠ 0) : M ≃ₗ[𝕜] M :=
  have : IsUnit (LinearMap.toMatrix (Module.finBasis 𝕜 M)
      (Module.finBasis 𝕜 M) f).det := by
    rw [LinearMap.det_toMatrix]
    exact isUnit_iff_ne_zero.2 hf
  LinearEquiv.ofIsUnitDet this

theorem LinearMap.associated_det_of_eq_comp (e : M ≃ₗ[R] M) (f f' : M →ₗ[R] M)
    (h : ∀ x, f x = f' (e x)) : Associated (LinearMap.det f) (LinearMap.det f') := by
  suffices Associated (LinearMap.det (f' ∘ₗ ↑e)) (LinearMap.det f') by
    convert this using 2
    ext x
    exact h x
  rw [← mul_one (LinearMap.det f'), LinearMap.det_comp]
  exact Associated.mul_left _ (associated_one_iff_isUnit.mpr e.isUnit_det')

theorem LinearMap.associated_det_comp_equiv {N : Type*} [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) (e e' : M ≃ₗ[R] N) :
    Associated (LinearMap.det (f ∘ₗ ↑e)) (LinearMap.det (f ∘ₗ ↑e')) := by
  refine LinearMap.associated_det_of_eq_comp (e.trans e'.symm) _ _ ?_
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]

namespace Module.Basis

/-- The determinant of a family of vectors with respect to some basis, as an alternating
multilinear map. -/
nonrec def det : M [⋀^ι]→ₗ[R] R where
  toMultilinearMap :=
    MultilinearMap.mk' (fun v ↦ det (e.toMatrix v))
      (fun v i x y ↦ by
        simp only [e.toMatrix_update, map_add, Finsupp.coe_add, det_updateCol_add])
      (fun u i c x ↦ by
        simp only [e.toMatrix_update, Algebra.id.smul_eq_mul, LinearEquiv.map_smul]
        apply det_updateCol_smul)
  map_eq_zero_of_eq' := by
    intro v i j h hij
    dsimp
    rw [← Function.update_eq_self i v, h, ← det_transpose, e.toMatrix_update, ← updateRow_transpose,
      ← e.toMatrix_transpose_apply]
    apply det_zero_of_row_eq hij
    rw [updateRow_ne hij.symm, updateRow_self]

theorem det_apply (v : ι → M) : e.det v = Matrix.det (e.toMatrix v) :=
  rfl

theorem det_self : e.det e = 1 := by simp [e.det_apply]

@[simp]
theorem det_isEmpty [IsEmpty ι] : e.det = AlternatingMap.constOfIsEmpty R M ι 1 := by
  ext v
  exact Matrix.det_isEmpty

/-- `Basis.det` is not the zero map. -/
theorem det_ne_zero [Nontrivial R] : e.det ≠ 0 := fun h => by simpa [h] using e.det_self

theorem smul_det {G} [Group G] [DistribMulAction G M] [SMulCommClass G R M]
    (g : G) (v : ι → M) :
    (g • e).det v = e.det (g⁻¹ • v) := by
  simp_rw [det_apply, toMatrix_smul_left]

theorem is_basis_iff_det {v : ι → M} :
    LinearIndependent R v ∧ span R (Set.range v) = ⊤ ↔ IsUnit (e.det v) := by
  constructor
  · rintro ⟨hli, hspan⟩
    set v' := Basis.mk hli hspan.ge
    rw [e.det_apply]
    convert LinearEquiv.isUnit_det (LinearEquiv.refl R M) v' e using 2
    ext i j
    simp [v']
  · intro h
    rw [Basis.det_apply, Basis.toMatrix_eq_toMatrix_constr] at h
    set v' := Basis.map e (LinearEquiv.ofIsUnitDet h) with v'_def
    have : ⇑v' = v := by
      ext i
      rw [v'_def, Basis.map_apply, LinearEquiv.ofIsUnitDet_apply, e.constr_basis]
    rw [← this]
    exact ⟨v'.linearIndependent, v'.span_eq⟩

theorem isUnit_det (e' : Basis ι R M) : IsUnit (e.det e') :=
  (is_basis_iff_det e).mp ⟨e'.linearIndependent, e'.span_eq⟩

end Module.Basis

/-- Any alternating map to `R` where `ι` has the cardinality of a basis equals the determinant
map with respect to that basis, multiplied by the value of that alternating map on that basis. -/
theorem AlternatingMap.eq_smul_basis_det (f : M [⋀^ι]→ₗ[R] R) : f = f e • e.det := by
  refine Basis.ext_alternating e fun i h => ?_
  let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  change f (e ∘ σ) = (f e • e.det) (e ∘ σ)
  simp [AlternatingMap.map_perm, Basis.det_self]

@[simp]
theorem AlternatingMap.map_basis_eq_zero_iff {ι : Type*} [Finite ι] (e : Basis ι R M)
    (f : M [⋀^ι]→ₗ[R] R) : f e = 0 ↔ f = 0 :=
  ⟨fun h => by
    cases nonempty_fintype ι
    letI := Classical.decEq ι
    simpa [h] using f.eq_smul_basis_det e,
   fun h => h.symm ▸ AlternatingMap.zero_apply _⟩

theorem AlternatingMap.map_basis_ne_zero_iff {ι : Type*} [Finite ι] (e : Basis ι R M)
    (f : M [⋀^ι]→ₗ[R] R) : f e ≠ 0 ↔ f ≠ 0 :=
  not_congr <| f.map_basis_eq_zero_iff e

variable {A : Type*} [CommRing A] [Module A M]

namespace Module.Basis

@[simp]
theorem det_comp (e : Basis ι A M) (f : M →ₗ[A] M) (v : ι → M) :
    e.det (f ∘ v) = (LinearMap.det f) * e.det v := by
  rw [det_apply, det_apply, ← f.det_toMatrix e, ← Matrix.det_mul,
    e.toMatrix_eq_toMatrix_constr (f ∘ v), e.toMatrix_eq_toMatrix_constr v, ← toMatrix_comp,
    e.constr_comp]

@[simp]
theorem det_comp_basis [Module A M'] (b : Basis ι A M) (b' : Basis ι A M') (f : M →ₗ[A] M') :
    b'.det (f ∘ b) = LinearMap.det (f ∘ₗ (b'.equiv b (Equiv.refl ι) : M' →ₗ[A] M)) := by
  rw [det_apply, ← LinearMap.det_toMatrix b', LinearMap.toMatrix_comp _ b, Matrix.det_mul,
    LinearMap.toMatrix_basis_equiv, Matrix.det_one, mul_one]
  congr 1; ext i j
  rw [toMatrix_apply, LinearMap.toMatrix_apply, Function.comp_apply]

@[simp]
theorem det_basis (b : Basis ι A M) (b' : Basis ι A M) :
    LinearMap.det (b'.equiv b (Equiv.refl ι)).toLinearMap = b'.det b :=
  (b.det_comp_basis b' (LinearMap.id)).symm

theorem det_mul_det (b b' b'' : Basis ι A M) :
    b.det b' * b'.det b'' = b.det b'' := by
  have : b'' = (b'.equiv b'' (Equiv.refl ι)).toLinearMap ∘ b'  := by
    ext; simp
  conv_rhs =>
    rw [this, Basis.det_comp, det_basis, mul_comm]

theorem det_inv (b : Basis ι A M) (b' : Basis ι A M) :
    (b.isUnit_det b').unit⁻¹ = b'.det b := by
  rw [← Units.mul_eq_one_iff_inv_eq, IsUnit.unit_spec, ← det_basis, ← det_basis]
  exact LinearEquiv.det_mul_det_symm _

theorem det_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M) (v : ι' → M)
    (e : ι ≃ ι') : (b.reindex e).det v = b.det (v ∘ e) := by
  rw [det_apply, toMatrix_reindex', det_reindexAlgEquiv, det_apply]

theorem det_reindex' {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M)
    (e : ι ≃ ι') : (b.reindex e).det = b.det.domDomCongr e :=
  AlternatingMap.ext fun _ => det_reindex _ _ _

theorem det_reindex_symm {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M)
    (v : ι → M) (e : ι' ≃ ι) : (b.reindex e.symm).det (v ∘ e) = b.det v := by
  rw [det_reindex, Function.comp_assoc, e.self_comp_symm, Function.comp_id]

@[simp]
theorem det_map (b : Basis ι R M) (f : M ≃ₗ[R] M') (v : ι → M') :
    (b.map f).det v = b.det (f.symm ∘ v) := by
  rw [det_apply, toMatrix_map, det_apply]

theorem det_map' (b : Basis ι R M) (f : M ≃ₗ[R] M') :
    (b.map f).det = b.det.compLinearMap f.symm :=
  AlternatingMap.ext <| b.det_map f

end Module.Basis

@[simp]
theorem Pi.basisFun_det : (Pi.basisFun R ι).det = Matrix.detRowAlternating := by
  ext M
  rw [Basis.det_apply, Basis.coePiBasisFun.toMatrix_eq_transpose, det_transpose]

theorem Pi.basisFun_det_apply (v : ι → ι → R) :
    (Pi.basisFun R ι).det v = (Matrix.of v).det := by
  rw [Pi.basisFun_det]
  rfl

namespace Module.Basis

/-- If we fix a background basis `e`, then for any other basis `v`, we can characterise the
coordinates provided by `v` in terms of determinants relative to `e`. -/
theorem det_smul_mk_coord_eq_det_update {v : ι → M} (hli : LinearIndependent R v)
    (hsp : ⊤ ≤ span R (range v)) (i : ι) :
    e.det v • (Basis.mk hli hsp).coord i = e.det.toMultilinearMap.toLinearMap v i := by
  apply (Basis.mk hli hsp).ext
  intro k
  rcases eq_or_ne k i with (rfl | hik) <;>
    simp only [Algebra.id.smul_eq_mul, coe_mk, LinearMap.smul_apply,
      MultilinearMap.toLinearMap_apply]
  · rw [mk_coord_apply_eq, mul_one, update_eq_self]
    congr
  · rw [mk_coord_apply_ne hik, mul_zero, eq_comm]
    exact e.det.map_eq_zero_of_eq _ (by simp [hik]) hik

/-- If a basis is multiplied columnwise by scalars `w : ι → Rˣ`, then the determinant with respect
to this basis is multiplied by the product of the inverse of these scalars. -/
theorem det_unitsSMul (e : Basis ι R M) (w : ι → Rˣ) :
    (e.unitsSMul w).det = (↑(∏ i, w i)⁻¹ : R) • e.det := by
  ext f
  change
    (Matrix.det fun i j => (e.unitsSMul w).repr (f j) i) =
      (↑(∏ i, w i)⁻¹ : R) • Matrix.det fun i j => e.repr (f j) i
  simp only [e.repr_unitsSMul]
  convert Matrix.det_mul_column (fun i => (↑(w i)⁻¹ : R)) fun i j => e.repr (f j) i
  simp [← Finset.prod_inv_distrib]

/-- The determinant of a basis constructed by `unitsSMul` is the product of the given units. -/
@[simp]
theorem det_unitsSMul_self (w : ι → Rˣ) : e.det (e.unitsSMul w) = ∏ i, (w i : R) := by
  simp [det_apply]

/-- The determinant of a basis constructed by `isUnitSMul` is the product of the given units. -/
@[simp]
theorem det_isUnitSMul {w : ι → R} (hw : ∀ i, IsUnit (w i)) :
    e.det (e.isUnitSMul hw) = ∏ i, w i :=
  e.det_unitsSMul_self _

end Module.Basis
