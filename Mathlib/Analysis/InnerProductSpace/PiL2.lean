/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Sébastien Gouëzel, Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.UnitaryGroup

#align_import analysis.inner_product_space.pi_L2 from "leanprover-community/mathlib"@"13bce9a6b6c44f6b4c91ac1c1d2a816e2533d395"

/-!
# `L²` inner product space structure on finite products of inner product spaces

The `L²` norm on a finite product of inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \sum \langle x_i, y_i \rangle.
$$
This is recorded in this file as an inner product space instance on `PiLp 2`.

This file develops the notion of a finite dimensional Hilbert space over `𝕜 = ℂ, ℝ`, referred to as
`E`. We define an `OrthonormalBasis 𝕜 ι E` as a linear isometric equivalence
between `E` and `EuclideanSpace 𝕜 ι`. Then `stdOrthonormalBasis` shows that such an equivalence
always exists if `E` is finite dimensional. We provide language for converting between a basis
that is orthonormal and an orthonormal basis (e.g. `Basis.toOrthonormalBasis`). We show that
orthonormal bases for each summand in a direct sum of spaces can be combined into an orthonormal
basis for the whole sum in `DirectSum.IsInternal.subordinateOrthonormalBasis`. In
the last section, various properties of matrices are explored.

## Main definitions

- `EuclideanSpace 𝕜 n`: defined to be `PiLp 2 (n → 𝕜)` for any `Fintype n`, i.e., the space
  from functions to `n` to `𝕜` with the `L²` norm. We register several instances on it (notably
  that it is a finite-dimensional inner product space).

- `OrthonormalBasis 𝕜 ι`: defined to be an isometry to Euclidean space from a given
  finite-dimensional inner product space, `E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι`.

- `Basis.toOrthonormalBasis`: constructs an `OrthonormalBasis` for a finite-dimensional
  Euclidean space from a `Basis` which is `Orthonormal`.

- `Orthonormal.exists_orthonormalBasis_extension`: provides an existential result of an
  `OrthonormalBasis` extending a given orthonormal set

- `exists_orthonormalBasis`: provides an orthonormal basis on a finite dimensional vector space

- `stdOrthonormalBasis`: provides an arbitrarily-chosen `OrthonormalBasis` of a given finite
  dimensional inner product space

For consequences in infinite dimension (Hilbert bases, etc.), see the file
`Analysis.InnerProductSpace.L2Space`.

-/

set_option linter.uppercaseLean3 false

open Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum

noncomputable section

variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `PiLp 2 f` for the product space, which is endowed with the `L^2` norm.
-/
instance PiLp.innerProductSpace {ι : Type*} [Fintype ι] (f : ι → Type*)
    [∀ i, NormedAddCommGroup (f i)] [∀ i, InnerProductSpace 𝕜 (f i)] :
    InnerProductSpace 𝕜 (PiLp 2 f) where
  inner x y := ∑ i, inner (x i) (y i)
  norm_sq_eq_inner x := by
    simp only [PiLp.norm_sq_eq_of_L2, map_sum, ← norm_sq_eq_inner, one_div]
  conj_symm := by
    intro x y
    unfold inner
    rw [map_sum]
    apply Finset.sum_congr rfl
    rintro z -
    apply inner_conj_symm
  add_left x y z :=
    show (∑ i, inner (x i + y i) (z i)) = (∑ i, inner (x i) (z i)) + ∑ i, inner (y i) (z i) by
      simp only [inner_add_left, Finset.sum_add_distrib]
  smul_left x y r :=
    show (∑ i : ι, inner (r • x i) (y i)) = conj r * ∑ i, inner (x i) (y i) by
      simp only [Finset.mul_sum, inner_smul_left]
#align pi_Lp.inner_product_space PiLp.innerProductSpace

@[simp]
theorem PiLp.inner_apply {ι : Type*} [Fintype ι] {f : ι → Type*} [∀ i, NormedAddCommGroup (f i)]
    [∀ i, InnerProductSpace 𝕜 (f i)] (x y : PiLp 2 f) : ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
  rfl
#align pi_Lp.inner_apply PiLp.inner_apply

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `EuclideanSpace 𝕜 (Fin n)`. -/
abbrev EuclideanSpace (𝕜 : Type*) (n : Type*) : Type _ :=
  PiLp 2 fun _ : n => 𝕜
#align euclidean_space EuclideanSpace

theorem EuclideanSpace.nnnorm_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖₊ = NNReal.sqrt (∑ i, ‖x i‖₊ ^ 2) :=
  PiLp.nnnorm_eq_of_L2 x
#align euclidean_space.nnnorm_eq EuclideanSpace.nnnorm_eq

theorem EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2) := by
  simpa only [Real.coe_sqrt, NNReal.coe_sum] using congr_arg ((↑) : ℝ≥0 → ℝ) x.nnnorm_eq
#align euclidean_space.norm_eq EuclideanSpace.norm_eq

theorem EuclideanSpace.dist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : dist x y = √(∑ i, dist (x i) (y i) ^ 2) :=
  PiLp.dist_eq_of_L2 x y
#align euclidean_space.dist_eq EuclideanSpace.dist_eq

theorem EuclideanSpace.nndist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : nndist x y = NNReal.sqrt (∑ i, nndist (x i) (y i) ^ 2) :=
  PiLp.nndist_eq_of_L2 x y
#align euclidean_space.nndist_eq EuclideanSpace.nndist_eq

theorem EuclideanSpace.edist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) :=
  PiLp.edist_eq_of_L2 x y
#align euclidean_space.edist_eq EuclideanSpace.edist_eq

theorem EuclideanSpace.ball_zero_eq {n : Type*} [Fintype n] (r : ℝ) (hr : 0 ≤ r) :
    Metric.ball (0 : EuclideanSpace ℝ n) r = {x | ∑ i, x i ^ 2 < r ^ 2} := by
  ext x
  have : (0 : ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [mem_setOf, mem_ball_zero_iff, norm_eq, norm_eq_abs, sq_abs, sqrt_lt this hr]

theorem EuclideanSpace.closedBall_zero_eq {n : Type*} [Fintype n] (r : ℝ) (hr : 0 ≤ r) :
    Metric.closedBall (0 : EuclideanSpace ℝ n) r = {x | ∑ i, x i ^ 2 ≤ r ^ 2} := by
  ext
  simp_rw [mem_setOf, mem_closedBall_zero_iff, norm_eq, norm_eq_abs, sq_abs, sqrt_le_left hr]

theorem EuclideanSpace.sphere_zero_eq {n : Type*} [Fintype n] (r : ℝ) (hr : 0 ≤ r) :
    Metric.sphere (0 : EuclideanSpace ℝ n) r = {x | ∑ i, x i ^ 2 = r ^ 2} := by
  ext x
  have : (0 : ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [mem_setOf, mem_sphere_zero_iff_norm, norm_eq, norm_eq_abs, sq_abs,
    Real.sqrt_eq_iff_sq_eq this hr, eq_comm]

section

#align euclidean_space.finite_dimensional WithLp.instModuleFinite

variable [Fintype ι]

#align euclidean_space.inner_product_space PiLp.innerProductSpace

@[simp]
theorem finrank_euclideanSpace :
    FiniteDimensional.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by
  simp [EuclideanSpace, PiLp, WithLp]
#align finrank_euclidean_space finrank_euclideanSpace

theorem finrank_euclideanSpace_fin {n : ℕ} :
    FiniteDimensional.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n := by simp
#align finrank_euclidean_space_fin finrank_euclideanSpace_fin

theorem EuclideanSpace.inner_eq_star_dotProduct (x y : EuclideanSpace 𝕜 ι) :
    ⟪x, y⟫ = Matrix.dotProduct (star <| WithLp.equiv _ _ x) (WithLp.equiv _ _ y) :=
  rfl
#align euclidean_space.inner_eq_star_dot_product EuclideanSpace.inner_eq_star_dotProduct

theorem EuclideanSpace.inner_piLp_equiv_symm (x y : ι → 𝕜) :
    ⟪(WithLp.equiv 2 _).symm x, (WithLp.equiv 2 _).symm y⟫ = Matrix.dotProduct (star x) y :=
  rfl
#align euclidean_space.inner_pi_Lp_equiv_symm EuclideanSpace.inner_piLp_equiv_symm

/-- A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce an isometry
from `E` to `PiLp 2` of the subspaces equipped with the `L2` inner product. -/
def DirectSum.IsInternal.isometryL2OfOrthogonalFamily [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : DirectSum.IsInternal V)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    E ≃ₗᵢ[𝕜] PiLp 2 fun i => V i := by
  let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
  let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
  refine LinearEquiv.isometryOfInner (e₂.symm.trans e₁) ?_
  suffices ∀ (v w : PiLp 2 fun i => V i), ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫ by
    intro v₀ w₀
    convert this (e₁ (e₂.symm v₀)) (e₁ (e₂.symm w₀)) <;>
      simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  intro v w
  trans ⟪∑ i, (V i).subtypeₗᵢ (v i), ∑ i, (V i).subtypeₗᵢ (w i)⟫
  · simp only [sum_inner, hV'.inner_right_fintype, PiLp.inner_apply]
  · congr <;> simp
#align direct_sum.is_internal.isometry_L2_of_orthogonal_family DirectSum.IsInternal.isometryL2OfOrthogonalFamily

@[simp]
theorem DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply [DecidableEq ι]
    {V : ι → Submodule 𝕜 E} (hV : DirectSum.IsInternal V)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (w : PiLp 2 fun i => V i) :
    (hV.isometryL2OfOrthogonalFamily hV').symm w = ∑ i, (w i : E) := by
  classical
    let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
    let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
    suffices ∀ v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i by exact this (e₁.symm w)
    intro v
    -- Porting note: added `DFinsupp.lsum`
    simp [e₁, e₂, DirectSum.coeLinearMap, DirectSum.toModule, DFinsupp.lsum,
      DFinsupp.sumAddHom_apply]
#align direct_sum.is_internal.isometry_L2_of_orthogonal_family_symm_apply DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply

end

variable (ι 𝕜)

/-- A shorthand for `PiLp.continuousLinearEquiv`. -/
abbrev EuclideanSpace.equiv : EuclideanSpace 𝕜 ι ≃L[𝕜] ι → 𝕜 :=
  PiLp.continuousLinearEquiv 2 𝕜 _
#align euclidean_space.equiv EuclideanSpace.equiv
#noalign euclidean_space.equiv_to_linear_equiv_apply
#noalign euclidean_space.equiv_apply
#noalign euclidean_space.equiv_to_linear_equiv_symm_apply
#noalign euclidean_space.equiv_symm_apply

variable {ι 𝕜}

-- TODO : This should be generalized to `PiLp`.
/-- The projection on the `i`-th coordinate of `EuclideanSpace 𝕜 ι`, as a linear map. -/
@[simps!]
def EuclideanSpace.projₗ (i : ι) : EuclideanSpace 𝕜 ι →ₗ[𝕜] 𝕜 :=
  (LinearMap.proj i).comp (WithLp.linearEquiv 2 𝕜 (ι → 𝕜) : EuclideanSpace 𝕜 ι →ₗ[𝕜] ι → 𝕜)
#align euclidean_space.projₗ EuclideanSpace.projₗ
#align euclidean_space.projₗ_apply EuclideanSpace.projₗ_apply

-- TODO : This should be generalized to `PiLp`.
/-- The projection on the `i`-th coordinate of `EuclideanSpace 𝕜 ι`,
as a continuous linear map. -/
@[simps! apply coe]
def EuclideanSpace.proj (i : ι) : EuclideanSpace 𝕜 ι →L[𝕜] 𝕜 :=
  ⟨EuclideanSpace.projₗ i, continuous_apply i⟩
#align euclidean_space.proj EuclideanSpace.proj
#align euclidean_space.proj_coe EuclideanSpace.proj_coe
#align euclidean_space.proj_apply EuclideanSpace.proj_apply

section DecEq

variable [DecidableEq ι]

-- TODO : This should be generalized to `PiLp`.
/-- The vector given in euclidean space by being `a : 𝕜` at coordinate `i : ι` and `0 : 𝕜` at
all other coordinates. -/
def EuclideanSpace.single (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι :=
  (WithLp.equiv _ _).symm (Pi.single i a)
#align euclidean_space.single EuclideanSpace.single

@[simp]
theorem WithLp.equiv_single (i : ι) (a : 𝕜) :
    WithLp.equiv _ _ (EuclideanSpace.single i a) = Pi.single i a :=
  rfl
#align pi_Lp.equiv_single WithLp.equiv_single

@[simp]
theorem WithLp.equiv_symm_single (i : ι) (a : 𝕜) :
    (WithLp.equiv _ _).symm (Pi.single i a) = EuclideanSpace.single i a :=
  rfl
#align pi_Lp.equiv_symm_single WithLp.equiv_symm_single

@[simp]
theorem EuclideanSpace.single_apply (i : ι) (a : 𝕜) (j : ι) :
    (EuclideanSpace.single i a) j = ite (j = i) a 0 := by
  rw [EuclideanSpace.single, WithLp.equiv_symm_pi_apply, ← Pi.single_apply i a j]
#align euclidean_space.single_apply EuclideanSpace.single_apply

variable [Fintype ι]

theorem EuclideanSpace.inner_single_left (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) :
    ⟪EuclideanSpace.single i (a : 𝕜), v⟫ = conj a * v i := by simp [apply_ite conj]
#align euclidean_space.inner_single_left EuclideanSpace.inner_single_left

theorem EuclideanSpace.inner_single_right (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) :
    ⟪v, EuclideanSpace.single i (a : 𝕜)⟫ = a * conj (v i) := by simp [apply_ite conj, mul_comm]
#align euclidean_space.inner_single_right EuclideanSpace.inner_single_right

@[simp]
theorem EuclideanSpace.norm_single (i : ι) (a : 𝕜) :
    ‖EuclideanSpace.single i (a : 𝕜)‖ = ‖a‖ :=
  PiLp.norm_equiv_symm_single 2 (fun _ => 𝕜) i a
#align euclidean_space.norm_single EuclideanSpace.norm_single

@[simp]
theorem EuclideanSpace.nnnorm_single (i : ι) (a : 𝕜) :
    ‖EuclideanSpace.single i (a : 𝕜)‖₊ = ‖a‖₊ :=
  PiLp.nnnorm_equiv_symm_single 2 (fun _ => 𝕜) i a
#align euclidean_space.nnnorm_single EuclideanSpace.nnnorm_single

@[simp]
theorem EuclideanSpace.dist_single_same (i : ι) (a b : 𝕜) :
    dist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = dist a b :=
  PiLp.dist_equiv_symm_single_same 2 (fun _ => 𝕜) i a b
#align euclidean_space.dist_single_same EuclideanSpace.dist_single_same

@[simp]
theorem EuclideanSpace.nndist_single_same (i : ι) (a b : 𝕜) :
    nndist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = nndist a b :=
  PiLp.nndist_equiv_symm_single_same 2 (fun _ => 𝕜) i a b
#align euclidean_space.nndist_single_same EuclideanSpace.nndist_single_same

@[simp]
theorem EuclideanSpace.edist_single_same (i : ι) (a b : 𝕜) :
    edist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = edist a b :=
  PiLp.edist_equiv_symm_single_same 2 (fun _ => 𝕜) i a b
#align euclidean_space.edist_single_same EuclideanSpace.edist_single_same

/-- `EuclideanSpace.single` forms an orthonormal family. -/
theorem EuclideanSpace.orthonormal_single :
    Orthonormal 𝕜 fun i : ι => EuclideanSpace.single i (1 : 𝕜) := by
  simp_rw [orthonormal_iff_ite, EuclideanSpace.inner_single_left, map_one, one_mul,
    EuclideanSpace.single_apply]
  intros
  trivial
#align euclidean_space.orthonormal_single EuclideanSpace.orthonormal_single

theorem EuclideanSpace.piLpCongrLeft_single
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι) (i' : ι') (v : 𝕜) :
    LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e (EuclideanSpace.single i' v) =
      EuclideanSpace.single (e i') v :=
  LinearIsometryEquiv.piLpCongrLeft_single e i' _
#align euclidean_space.pi_Lp_congr_left_single EuclideanSpace.piLpCongrLeft_single

end DecEq

variable (ι 𝕜 E)
variable [Fintype ι]

/-- An orthonormal basis on E is an identification of `E` with its dimensional-matching
`EuclideanSpace 𝕜 ι`. -/
structure OrthonormalBasis where ofRepr ::
  /-- Linear isometry between `E` and `EuclideanSpace 𝕜 ι` representing the orthonormal basis. -/
  repr : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι
#align orthonormal_basis OrthonormalBasis
#align orthonormal_basis.of_repr OrthonormalBasis.ofRepr
#align orthonormal_basis.repr OrthonormalBasis.repr

variable {ι 𝕜 E}

namespace OrthonormalBasis

theorem repr_injective :
    Injective (repr : OrthonormalBasis ι 𝕜 E → E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) := fun f g h => by
  cases f
  cases g
  congr

-- Porting note: `CoeFun` → `FunLike`
/-- `b i` is the `i`th basis vector. -/
instance instFunLike : FunLike (OrthonormalBasis ι 𝕜 E) ι E where
  coe b i := by classical exact b.repr.symm (EuclideanSpace.single i (1 : 𝕜))
  coe_injective' b b' h := repr_injective <| LinearIsometryEquiv.toLinearEquiv_injective <|
    LinearEquiv.symm_bijective.injective <| LinearEquiv.toLinearMap_injective <| by
      classical
        rw [← LinearMap.cancel_right (WithLp.linearEquiv 2 𝕜 (_ → 𝕜)).symm.surjective]
        simp only [LinearIsometryEquiv.toLinearEquiv_symm]
        refine LinearMap.pi_ext fun i k => ?_
        have : k = k • (1 : 𝕜) := by rw [smul_eq_mul, mul_one]
        rw [this, Pi.single_smul]
        replace h := congr_fun h i
        simp only [LinearEquiv.comp_coe, map_smul, LinearEquiv.coe_coe,
          LinearEquiv.trans_apply, WithLp.linearEquiv_symm_apply, WithLp.equiv_symm_single,
          LinearIsometryEquiv.coe_toLinearEquiv] at h ⊢
        rw [h]

#noalign orthonormal_basis.has_coe_to_fun

@[simp]
theorem coe_ofRepr [DecidableEq ι] (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) :
    ⇑(OrthonormalBasis.ofRepr e) = fun i => e.symm (EuclideanSpace.single i (1 : 𝕜)) := by
  -- Porting note: simplified with `congr!`
  dsimp only [DFunLike.coe]
  funext
  congr!
#align orthonormal_basis.coe_of_repr OrthonormalBasis.coe_ofRepr

@[simp]
protected theorem repr_symm_single [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr.symm (EuclideanSpace.single i (1 : 𝕜)) = b i := by
  -- Porting note: simplified with `congr!`
  dsimp only [DFunLike.coe]
  congr!
#align orthonormal_basis.repr_symm_single OrthonormalBasis.repr_symm_single

@[simp]
protected theorem repr_self [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = EuclideanSpace.single i (1 : 𝕜) := by
  rw [← b.repr_symm_single i, LinearIsometryEquiv.apply_symm_apply]
#align orthonormal_basis.repr_self OrthonormalBasis.repr_self

protected theorem repr_apply_apply (b : OrthonormalBasis ι 𝕜 E) (v : E) (i : ι) :
    b.repr v i = ⟪b i, v⟫ := by
  classical
    rw [← b.repr.inner_map_map (b i) v, b.repr_self i, EuclideanSpace.inner_single_left]
    simp only [one_mul, eq_self_iff_true, map_one]
#align orthonormal_basis.repr_apply_apply OrthonormalBasis.repr_apply_apply

@[simp]
protected theorem orthonormal (b : OrthonormalBasis ι 𝕜 E) : Orthonormal 𝕜 b := by
  classical
    rw [orthonormal_iff_ite]
    intro i j
    rw [← b.repr.inner_map_map (b i) (b j), b.repr_self i, b.repr_self j,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, map_one, one_mul]
#align orthonormal_basis.orthonormal OrthonormalBasis.orthonormal

/-- The `Basis ι 𝕜 E` underlying the `OrthonormalBasis` -/
protected def toBasis (b : OrthonormalBasis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.ofEquivFun b.repr.toLinearEquiv
#align orthonormal_basis.to_basis OrthonormalBasis.toBasis

@[simp]
protected theorem coe_toBasis (b : OrthonormalBasis ι 𝕜 E) : (⇑b.toBasis : ι → E) = ⇑b := by
  rw [OrthonormalBasis.toBasis] -- Porting note: was `change`
  ext j
  classical
    rw [Basis.coe_ofEquivFun]
    congr
#align orthonormal_basis.coe_to_basis OrthonormalBasis.coe_toBasis

@[simp]
protected theorem coe_toBasis_repr (b : OrthonormalBasis ι 𝕜 E) :
    b.toBasis.equivFun = b.repr.toLinearEquiv :=
  Basis.equivFun_ofEquivFun _
#align orthonormal_basis.coe_to_basis_repr OrthonormalBasis.coe_toBasis_repr

@[simp]
protected theorem coe_toBasis_repr_apply (b : OrthonormalBasis ι 𝕜 E) (x : E) (i : ι) :
    b.toBasis.repr x i = b.repr x i := by
  rw [← Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr];
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [LinearIsometryEquiv.coe_toLinearEquiv]
#align orthonormal_basis.coe_to_basis_repr_apply OrthonormalBasis.coe_toBasis_repr_apply

protected theorem sum_repr (b : OrthonormalBasis ι 𝕜 E) (x : E) : ∑ i, b.repr x i • b i = x := by
  simp_rw [← b.coe_toBasis_repr_apply, ← b.coe_toBasis]
  exact b.toBasis.sum_repr x
#align orthonormal_basis.sum_repr OrthonormalBasis.sum_repr

protected theorem sum_repr_symm (b : OrthonormalBasis ι 𝕜 E) (v : EuclideanSpace 𝕜 ι) :
    ∑ i, v i • b i = b.repr.symm v := by simpa using (b.toBasis.equivFun_symm_apply v).symm
#align orthonormal_basis.sum_repr_symm OrthonormalBasis.sum_repr_symm

protected theorem sum_inner_mul_inner (b : OrthonormalBasis ι 𝕜 E) (x y : E) :
    ∑ i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ := by
  have := congr_arg (innerSL 𝕜 x) (b.sum_repr y)
  rw [map_sum] at this
  convert this
  rw [map_smul, b.repr_apply_apply, mul_comm]
  simp only [innerSL_apply, smul_eq_mul] -- Porting note: was `rfl`
#align orthonormal_basis.sum_inner_mul_inner OrthonormalBasis.sum_inner_mul_inner

protected theorem orthogonalProjection_eq_sum {U : Submodule 𝕜 E} [CompleteSpace U]
    (b : OrthonormalBasis ι 𝕜 U) (x : E) :
    orthogonalProjection U x = ∑ i, ⟪(b i : E), x⟫ • b i := by
  simpa only [b.repr_apply_apply, inner_orthogonalProjection_eq_of_mem_left] using
    (b.sum_repr (orthogonalProjection U x)).symm
#align orthonormal_basis.orthogonal_projection_eq_sum OrthonormalBasis.orthogonalProjection_eq_sum

/-- Mapping an orthonormal basis along a `LinearIsometryEquiv`. -/
protected def map {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) : OrthonormalBasis ι 𝕜 G where
  repr := L.symm.trans b.repr
#align orthonormal_basis.map OrthonormalBasis.map

@[simp]
protected theorem map_apply {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) (i : ι) : b.map L i = L (b i) :=
  rfl
#align orthonormal_basis.map_apply OrthonormalBasis.map_apply

@[simp]
protected theorem toBasis_map {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) :
    (b.map L).toBasis = b.toBasis.map L.toLinearEquiv :=
  rfl
#align orthonormal_basis.to_basis_map OrthonormalBasis.toBasis_map

/-- A basis that is orthonormal is an orthonormal basis. -/
def _root_.Basis.toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.ofRepr <|
    LinearEquiv.isometryOfInner v.equivFun
      (by
        intro x y
        let p : EuclideanSpace 𝕜 ι := v.equivFun x
        let q : EuclideanSpace 𝕜 ι := v.equivFun y
        have key : ⟪p, q⟫ = ⟪∑ i, p i • v i, ∑ i, q i • v i⟫ := by
          simp [sum_inner, inner_smul_left, hv.inner_right_fintype]
        convert key
        · rw [← v.equivFun.symm_apply_apply x, v.equivFun_symm_apply]
        · rw [← v.equivFun.symm_apply_apply y, v.equivFun_symm_apply])
#align basis.to_orthonormal_basis Basis.toOrthonormalBasis

@[simp]
theorem _root_.Basis.coe_toOrthonormalBasis_repr (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr : E → EuclideanSpace 𝕜 ι) = v.equivFun :=
  rfl
#align basis.coe_to_orthonormal_basis_repr Basis.coe_toOrthonormalBasis_repr

@[simp]
theorem _root_.Basis.coe_toOrthonormalBasis_repr_symm (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr.symm : EuclideanSpace 𝕜 ι → E) = v.equivFun.symm :=
  rfl
#align basis.coe_to_orthonormal_basis_repr_symm Basis.coe_toOrthonormalBasis_repr_symm

@[simp]
theorem _root_.Basis.toBasis_toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv).toBasis = v := by
  simp [Basis.toOrthonormalBasis, OrthonormalBasis.toBasis]
#align basis.to_basis_to_orthonormal_basis Basis.toBasis_toOrthonormalBasis

@[simp]
theorem _root_.Basis.coe_toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv : ι → E) = (v : ι → E) :=
  calc
    (v.toOrthonormalBasis hv : ι → E) = ((v.toOrthonormalBasis hv).toBasis : ι → E) := by
      classical rw [OrthonormalBasis.coe_toBasis]
    _ = (v : ι → E) := by simp
#align basis.coe_to_orthonormal_basis Basis.coe_toOrthonormalBasis

/-- `Pi.orthonormalBasis (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i))` is the
`Σ i, ι i`-indexed orthonormal basis on `Π i, E i` given by `B i` on each component. -/
protected def _root_.Pi.orthonormalBasis {η : Type*} [Fintype η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i)) :
    OrthonormalBasis ((i : η) × ι i) 𝕜 (PiLp 2 E) where
  repr := .trans
      (.piLpCongrRight 2 fun i => (B i).repr)
      (.symm <| .piLpCurry 𝕜 2 fun _ _ => 𝕜)

theorem _root_.Pi.orthonormalBasis.toBasis {η : Type*} [Fintype η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i)) :
    (Pi.orthonormalBasis B).toBasis =
      ((Pi.basis fun i : η ↦ (B i).toBasis).map (WithLp.linearEquiv 2 _ _).symm) := by ext; rfl

@[simp]
theorem _root_.Pi.orthonormalBasis_apply {η : Type*} [Fintype η] [DecidableEq η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i))
    (j : (i : η) × (ι i)) :
    Pi.orthonormalBasis B j = (WithLp.equiv _ _).symm (Pi.single _ (B j.fst j.snd)) := by
  classical
  ext k
  obtain ⟨i, j⟩ := j
  simp only [Pi.orthonormalBasis, coe_ofRepr, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.piLpCongrRight_symm,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrRight_apply,
    LinearIsometryEquiv.piLpCurry_apply, WithLp.equiv_single, WithLp.equiv_symm_pi_apply,
    Sigma.curry_single (γ := fun _ _ => 𝕜)]
  obtain rfl | hi := Decidable.eq_or_ne i k
  · simp only [Pi.single_eq_same, WithLp.equiv_symm_single, OrthonormalBasis.repr_symm_single]
  · simp only [Pi.single_eq_of_ne' hi, WithLp.equiv_symm_zero, _root_.map_zero]

@[simp]
theorem _root_.Pi.orthonormalBasis_repr {η : Type*} [Fintype η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i)) (x : (i : η ) → E i)
    (j : (i : η) × (ι i)) :
    (Pi.orthonormalBasis B).repr x j = (B j.fst).repr (x j.fst) j.snd := rfl

variable {v : ι → E}

/-- A finite orthonormal set that spans is an orthonormal basis -/
protected def mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)) :
    OrthonormalBasis ι 𝕜 E :=
  (Basis.mk (Orthonormal.linearIndependent hon) hsp).toOrthonormalBasis (by rwa [Basis.coe_mk])
#align orthonormal_basis.mk OrthonormalBasis.mk

@[simp]
protected theorem coe_mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)) :
    ⇑(OrthonormalBasis.mk hon hsp) = v := by
  classical rw [OrthonormalBasis.mk, _root_.Basis.coe_toOrthonormalBasis, Basis.coe_mk]
#align orthonormal_basis.coe_mk OrthonormalBasis.coe_mk

/-- Any finite subset of an orthonormal family is an `OrthonormalBasis` for its span. -/
protected def span [DecidableEq E] {v' : ι' → E} (h : Orthonormal 𝕜 v') (s : Finset ι') :
    OrthonormalBasis s 𝕜 (span 𝕜 (s.image v' : Set E)) :=
  let e₀' : Basis s 𝕜 _ :=
    Basis.span (h.linearIndependent.comp ((↑) : s → ι') Subtype.val_injective)
  let e₀ : OrthonormalBasis s 𝕜 _ :=
    OrthonormalBasis.mk
      (by
        convert orthonormal_span (h.comp ((↑) : s → ι') Subtype.val_injective)
        simp [e₀', Basis.span_apply])
      e₀'.span_eq.ge
  let φ : span 𝕜 (s.image v' : Set E) ≃ₗᵢ[𝕜] span 𝕜 (range (v' ∘ ((↑) : s → ι'))) :=
    LinearIsometryEquiv.ofEq _ _
      (by
        rw [Finset.coe_image, image_eq_range]
        rfl)
  e₀.map φ.symm
#align orthonormal_basis.span OrthonormalBasis.span

@[simp]
protected theorem span_apply [DecidableEq E] {v' : ι' → E} (h : Orthonormal 𝕜 v') (s : Finset ι')
    (i : s) : (OrthonormalBasis.span h s i : E) = v' i := by
  simp only [OrthonormalBasis.span, Basis.span_apply, LinearIsometryEquiv.ofEq_symm,
    OrthonormalBasis.map_apply, OrthonormalBasis.coe_mk, LinearIsometryEquiv.coe_ofEq_apply,
    comp_apply]
#align orthonormal_basis.span_apply OrthonormalBasis.span_apply

open Submodule

/-- A finite orthonormal family of vectors whose span has trivial orthogonal complement is an
orthonormal basis. -/
protected def mkOfOrthogonalEqBot (hon : Orthonormal 𝕜 v) (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) :
    OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk hon
    (by
      refine Eq.ge ?_
      haveI : FiniteDimensional 𝕜 (span 𝕜 (range v)) :=
        FiniteDimensional.span_of_finite 𝕜 (finite_range v)
      haveI : CompleteSpace (span 𝕜 (range v)) := FiniteDimensional.complete 𝕜 _
      rwa [orthogonal_eq_bot_iff] at hsp)
#align orthonormal_basis.mk_of_orthogonal_eq_bot OrthonormalBasis.mkOfOrthogonalEqBot

@[simp]
protected theorem coe_of_orthogonal_eq_bot_mk (hon : Orthonormal 𝕜 v)
    (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) : ⇑(OrthonormalBasis.mkOfOrthogonalEqBot hon hsp) = v :=
  OrthonormalBasis.coe_mk hon _
#align orthonormal_basis.coe_of_orthogonal_eq_bot_mk OrthonormalBasis.coe_of_orthogonal_eq_bot_mk

variable [Fintype ι']

/-- `b.reindex (e : ι ≃ ι')` is an `OrthonormalBasis` indexed by `ι'` -/
def reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') : OrthonormalBasis ι' 𝕜 E :=
  OrthonormalBasis.ofRepr (b.repr.trans (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e))
#align orthonormal_basis.reindex OrthonormalBasis.reindex

protected theorem reindex_apply (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
    (b.reindex e) i' = b (e.symm i') := by
  classical
    dsimp [reindex]
    rw [coe_ofRepr]
    dsimp
    rw [← b.repr_symm_single, LinearIsometryEquiv.piLpCongrLeft_symm,
      EuclideanSpace.piLpCongrLeft_single]
#align orthonormal_basis.reindex_apply OrthonormalBasis.reindex_apply

@[simp]
theorem reindex_toBasis (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') :
    (b.reindex e).toBasis = b.toBasis.reindex e := Basis.eq_ofRepr_eq_repr fun _ ↦ congr_fun rfl

@[simp]
protected theorem coe_reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⇑(b.reindex e) = b ∘ e.symm :=
  funext (b.reindex_apply e)
#align orthonormal_basis.coe_reindex OrthonormalBasis.coe_reindex

@[simp]
protected theorem repr_reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (x : E) (i' : ι') :
    (b.reindex e).repr x i' = b.repr x (e.symm i') := by
  classical
  rw [OrthonormalBasis.repr_apply_apply, b.repr_apply_apply, OrthonormalBasis.coe_reindex,
    comp_apply]
#align orthonormal_basis.repr_reindex OrthonormalBasis.repr_reindex

end OrthonormalBasis

namespace EuclideanSpace

variable (𝕜 ι)

/-- The basis `Pi.basisFun`, bundled as an orthornormal basis of `EuclideanSpace 𝕜 ι`. -/
noncomputable def basisFun : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι) :=
  ⟨LinearIsometryEquiv.refl _ _⟩

@[simp]
theorem basisFun_apply [DecidableEq ι] (i : ι) : basisFun ι 𝕜 i = EuclideanSpace.single i 1 :=
  PiLp.basisFun_apply _ _ _ _

@[simp]
theorem basisFun_repr (x : EuclideanSpace 𝕜 ι) (i : ι) : (basisFun ι 𝕜).repr x i = x i := rfl

theorem basisFun_toBasis : (basisFun ι 𝕜).toBasis = PiLp.basisFun _ 𝕜 ι := rfl

end EuclideanSpace

instance OrthonormalBasis.instInhabited : Inhabited (OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) :=
  ⟨EuclideanSpace.basisFun ι 𝕜⟩
#align orthonormal_basis.inhabited OrthonormalBasis.instInhabited

section Complex

/-- `![1, I]` is an orthonormal basis for `ℂ` considered as a real inner product space. -/
def Complex.orthonormalBasisOneI : OrthonormalBasis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.toOrthonormalBasis
    (by
      rw [orthonormal_iff_ite]
      intro i; fin_cases i <;> intro j <;> fin_cases j <;> simp [real_inner_eq_re_inner])
#align complex.orthonormal_basis_one_I Complex.orthonormalBasisOneI

@[simp]
theorem Complex.orthonormalBasisOneI_repr_apply (z : ℂ) :
    Complex.orthonormalBasisOneI.repr z = ![z.re, z.im] :=
  rfl
#align complex.orthonormal_basis_one_I_repr_apply Complex.orthonormalBasisOneI_repr_apply

@[simp]
theorem Complex.orthonormalBasisOneI_repr_symm_apply (x : EuclideanSpace ℝ (Fin 2)) :
    Complex.orthonormalBasisOneI.repr.symm x = x 0 + x 1 * I :=
  rfl
#align complex.orthonormal_basis_one_I_repr_symm_apply Complex.orthonormalBasisOneI_repr_symm_apply

@[simp]
theorem Complex.toBasis_orthonormalBasisOneI :
    Complex.orthonormalBasisOneI.toBasis = Complex.basisOneI :=
  Basis.toBasis_toOrthonormalBasis _ _
#align complex.to_basis_orthonormal_basis_one_I Complex.toBasis_orthonormalBasisOneI

@[simp]
theorem Complex.coe_orthonormalBasisOneI :
    (Complex.orthonormalBasisOneI : Fin 2 → ℂ) = ![1, I] := by
  simp [Complex.orthonormalBasisOneI]
#align complex.coe_orthonormal_basis_one_I Complex.coe_orthonormalBasisOneI

/-- The isometry between `ℂ` and a two-dimensional real inner product space given by a basis. -/
def Complex.isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) ℝ F) : ℂ ≃ₗᵢ[ℝ] F :=
  Complex.orthonormalBasisOneI.repr.trans v.repr.symm
#align complex.isometry_of_orthonormal Complex.isometryOfOrthonormal

@[simp]
theorem Complex.map_isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) ℝ F) (f : F ≃ₗᵢ[ℝ] F') :
    Complex.isometryOfOrthonormal (v.map f) = (Complex.isometryOfOrthonormal v).trans f := by
  simp [Complex.isometryOfOrthonormal, LinearIsometryEquiv.trans_assoc, OrthonormalBasis.map]
  -- Porting note: `LinearIsometryEquiv.trans_assoc` doesn't trigger in the `simp` above
  rw [LinearIsometryEquiv.trans_assoc]
#align complex.map_isometry_of_orthonormal Complex.map_isometryOfOrthonormal

theorem Complex.isometryOfOrthonormal_symm_apply (v : OrthonormalBasis (Fin 2) ℝ F) (f : F) :
    (Complex.isometryOfOrthonormal v).symm f =
      (v.toBasis.coord 0 f : ℂ) + (v.toBasis.coord 1 f : ℂ) * I := by
  simp [Complex.isometryOfOrthonormal]
#align complex.isometry_of_orthonormal_symm_apply Complex.isometryOfOrthonormal_symm_apply

theorem Complex.isometryOfOrthonormal_apply (v : OrthonormalBasis (Fin 2) ℝ F) (z : ℂ) :
    Complex.isometryOfOrthonormal v z = z.re • v 0 + z.im • v 1 := by
  -- Porting note: was
  -- simp [Complex.isometryOfOrthonormal, ← v.sum_repr_symm]
  rw [Complex.isometryOfOrthonormal, LinearIsometryEquiv.trans_apply]
  simp [← v.sum_repr_symm]
#align complex.isometry_of_orthonormal_apply Complex.isometryOfOrthonormal_apply

end Complex

open FiniteDimensional

/-! ### Matrix representation of an orthonormal basis with respect to another -/


section ToMatrix

variable [DecidableEq ι]

section

variable (a b : OrthonormalBasis ι 𝕜 E)

/-- The change-of-basis matrix between two orthonormal bases `a`, `b` is a unitary matrix. -/
theorem OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary :
    a.toBasis.toMatrix b ∈ Matrix.unitaryGroup ι 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  convert a.repr.inner_map_map (b i) (b j)
  rw [orthonormal_iff_ite.mp b.orthonormal i j]
  rfl
#align orthonormal_basis.to_matrix_orthonormal_basis_mem_unitary OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary

/-- The determinant of the change-of-basis matrix between two orthonormal bases `a`, `b` has
unit length. -/
@[simp]
theorem OrthonormalBasis.det_to_matrix_orthonormalBasis : ‖a.toBasis.det b‖ = 1 := by
  have := (Matrix.det_of_mem_unitary (a.toMatrix_orthonormalBasis_mem_unitary b)).2
  rw [star_def, RCLike.mul_conj] at this
  norm_cast at this
  rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at this
#align orthonormal_basis.det_to_matrix_orthonormal_basis OrthonormalBasis.det_to_matrix_orthonormalBasis

end

section Real

variable (a b : OrthonormalBasis ι ℝ F)

/-- The change-of-basis matrix between two orthonormal bases `a`, `b` is an orthogonal matrix. -/
theorem OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal :
    a.toBasis.toMatrix b ∈ Matrix.orthogonalGroup ι ℝ :=
  a.toMatrix_orthonormalBasis_mem_unitary b
#align orthonormal_basis.to_matrix_orthonormal_basis_mem_orthogonal OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal

/-- The determinant of the change-of-basis matrix between two orthonormal bases `a`, `b` is ±1. -/
theorem OrthonormalBasis.det_to_matrix_orthonormalBasis_real :
    a.toBasis.det b = 1 ∨ a.toBasis.det b = -1 := by
  rw [← sq_eq_one_iff]
  simpa [unitary, sq] using Matrix.det_of_mem_unitary (a.toMatrix_orthonormalBasis_mem_unitary b)
#align orthonormal_basis.det_to_matrix_orthonormal_basis_real OrthonormalBasis.det_to_matrix_orthonormalBasis_real

end Real

end ToMatrix

/-! ### Existence of orthonormal basis, etc. -/


section FiniteDimensional

variable {v : Set E}
variable {A : ι → Submodule 𝕜 E}

/-- Given an internal direct sum decomposition of a module `M`, and an orthonormal basis for each
of the components of the direct sum, the disjoint union of these orthonormal bases is an
orthonormal basis for `M`. -/
noncomputable def DirectSum.IsInternal.collectedOrthonormalBasis
    (hV : OrthogonalFamily 𝕜 (fun i => A i) fun i => (A i).subtypeₗᵢ) [DecidableEq ι]
    (hV_sum : DirectSum.IsInternal fun i => A i) {α : ι → Type*} [∀ i, Fintype (α i)]
    (v_family : ∀ i, OrthonormalBasis (α i) 𝕜 (A i)) : OrthonormalBasis (Σi, α i) 𝕜 E :=
  (hV_sum.collectedBasis fun i => (v_family i).toBasis).toOrthonormalBasis <| by
    simpa using
      hV.orthonormal_sigma_orthonormal (show ∀ i, Orthonormal 𝕜 (v_family i).toBasis by simp)
#align direct_sum.is_internal.collected_orthonormal_basis DirectSum.IsInternal.collectedOrthonormalBasis

theorem DirectSum.IsInternal.collectedOrthonormalBasis_mem [DecidableEq ι]
    (h : DirectSum.IsInternal A) {α : ι → Type*} [∀ i, Fintype (α i)]
    (hV : OrthogonalFamily 𝕜 (fun i => A i) fun i => (A i).subtypeₗᵢ)
    (v : ∀ i, OrthonormalBasis (α i) 𝕜 (A i)) (a : Σi, α i) :
    h.collectedOrthonormalBasis hV v a ∈ A a.1 := by
  simp [DirectSum.IsInternal.collectedOrthonormalBasis]
#align direct_sum.is_internal.collected_orthonormal_basis_mem DirectSum.IsInternal.collectedOrthonormalBasis_mem

variable [FiniteDimensional 𝕜 E]

/-- In a finite-dimensional `InnerProductSpace`, any orthonormal subset can be extended to an
orthonormal basis. -/
theorem Orthonormal.exists_orthonormalBasis_extension (hv : Orthonormal 𝕜 ((↑) : v → E)) :
    ∃ (u : Finset E) (b : OrthonormalBasis u 𝕜 E), v ⊆ u ∧ ⇑b = ((↑) : u → E) := by
  obtain ⟨u₀, hu₀s, hu₀, hu₀_max⟩ := exists_maximal_orthonormal hv
  rw [maximal_orthonormal_iff_orthogonalComplement_eq_bot hu₀] at hu₀_max
  have hu₀_finite : u₀.Finite := hu₀.linearIndependent.setFinite
  let u : Finset E := hu₀_finite.toFinset
  let fu : ↥u ≃ ↥u₀ := hu₀_finite.subtypeEquivToFinset.symm
  have hu : Orthonormal 𝕜 ((↑) : u → E) := by simpa using hu₀.comp _ fu.injective
  refine ⟨u, OrthonormalBasis.mkOfOrthogonalEqBot hu ?_, ?_, ?_⟩
  · simpa [u] using hu₀_max
  · simpa [u] using hu₀s
  · simp
#align orthonormal.exists_orthonormal_basis_extension Orthonormal.exists_orthonormalBasis_extension

theorem Orthonormal.exists_orthonormalBasis_extension_of_card_eq {ι : Type*} [Fintype ι]
    (card_ι : finrank 𝕜 E = Fintype.card ι) {v : ι → E} {s : Set ι}
    (hv : Orthonormal 𝕜 (s.restrict v)) : ∃ b : OrthonormalBasis ι 𝕜 E, ∀ i ∈ s, b i = v i := by
  have hsv : Injective (s.restrict v) := hv.linearIndependent.injective
  have hX : Orthonormal 𝕜 ((↑) : Set.range (s.restrict v) → E) := by
    rwa [orthonormal_subtype_range hsv]
  obtain ⟨Y, b₀, hX, hb₀⟩ := hX.exists_orthonormalBasis_extension
  have hιY : Fintype.card ι = Y.card := by
    refine card_ι.symm.trans ?_
    exact FiniteDimensional.finrank_eq_card_finset_basis b₀.toBasis
  have hvsY : s.MapsTo v Y := (s.mapsTo_image v).mono_right (by rwa [← range_restrict])
  have hsv' : Set.InjOn v s := by
    rw [Set.injOn_iff_injective]
    exact hsv
  obtain ⟨g, hg⟩ := hvsY.exists_equiv_extend_of_card_eq hιY hsv'
  use b₀.reindex g.symm
  intro i hi
  simp [hb₀, hg i hi]
#align orthonormal.exists_orthonormal_basis_extension_of_card_eq Orthonormal.exists_orthonormalBasis_extension_of_card_eq

variable (𝕜 E)

/-- A finite-dimensional inner product space admits an orthonormal basis. -/
theorem _root_.exists_orthonormalBasis :
    ∃ (w : Finset E) (b : OrthonormalBasis w 𝕜 E), ⇑b = ((↑) : w → E) :=
  let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_orthonormalBasis_extension
  ⟨w, hw, hw''⟩
#align exists_orthonormal_basis exists_orthonormalBasis

/-- A finite-dimensional `InnerProductSpace` has an orthonormal basis. -/
irreducible_def stdOrthonormalBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E := by
  let b := Classical.choose (Classical.choose_spec <| exists_orthonormalBasis 𝕜 E)
  rw [finrank_eq_card_basis b.toBasis]
  exact b.reindex (Fintype.equivFinOfCardEq rfl)
#align std_orthonormal_basis stdOrthonormalBasis

/-- An orthonormal basis of `ℝ` is made either of the vector `1`, or of the vector `-1`. -/
theorem orthonormalBasis_one_dim (b : OrthonormalBasis ι ℝ ℝ) :
    (⇑b = fun _ => (1 : ℝ)) ∨ ⇑b = fun _ => (-1 : ℝ) := by
  have : Unique ι := b.toBasis.unique
  have : b default = 1 ∨ b default = -1 := by
    have : ‖b default‖ = 1 := b.orthonormal.1 _
    rwa [Real.norm_eq_abs, abs_eq (zero_le_one' ℝ)] at this
  rw [eq_const_of_unique b]
  refine this.imp ?_ ?_ <;> (intro; ext; simp [*])
#align orthonormal_basis_one_dim orthonormalBasis_one_dim

variable {𝕜 E}

section SubordinateOrthonormalBasis

open DirectSum

variable {n : ℕ} (hn : finrank 𝕜 E = n) [DecidableEq ι] {V : ι → Submodule 𝕜 E} (hV : IsInternal V)

/-- Exhibit a bijection between `Fin n` and the index set of a certain basis of an `n`-dimensional
inner product space `E`.  This should not be accessed directly, but only via the subsequent API. -/
irreducible_def DirectSum.IsInternal.sigmaOrthonormalBasisIndexEquiv
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    (Σi, Fin (finrank 𝕜 (V i))) ≃ Fin n :=
  let b := hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)
  Fintype.equivFinOfCardEq <| (FiniteDimensional.finrank_eq_card_basis b.toBasis).symm.trans hn
#align direct_sum.is_internal.sigma_orthonormal_basis_index_equiv DirectSum.IsInternal.sigmaOrthonormalBasisIndexEquiv

/-- An `n`-dimensional `InnerProductSpace` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `Fin n` and subordinate to that direct sum. -/
irreducible_def DirectSum.IsInternal.subordinateOrthonormalBasis
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    OrthonormalBasis (Fin n) 𝕜 E :=
  (hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)).reindex
    (hV.sigmaOrthonormalBasisIndexEquiv hn hV')
#align direct_sum.is_internal.subordinate_orthonormal_basis DirectSum.IsInternal.subordinateOrthonormalBasis

/-- An `n`-dimensional `InnerProductSpace` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `Fin n` and subordinate to that direct sum. This function
provides the mapping by which it is subordinate. -/
irreducible_def DirectSum.IsInternal.subordinateOrthonormalBasisIndex (a : Fin n)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) : ι :=
  ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a).1
#align direct_sum.is_internal.subordinate_orthonormal_basis_index DirectSum.IsInternal.subordinateOrthonormalBasisIndex

/-- The basis constructed in `DirectSum.IsInternal.subordinateOrthonormalBasis` is subordinate to
the `OrthogonalFamily` in question. -/
theorem DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate (a : Fin n)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    hV.subordinateOrthonormalBasis hn hV' a ∈ V (hV.subordinateOrthonormalBasisIndex hn a hV') := by
  simpa only [DirectSum.IsInternal.subordinateOrthonormalBasis, OrthonormalBasis.coe_reindex,
    DirectSum.IsInternal.subordinateOrthonormalBasisIndex] using
    hV.collectedOrthonormalBasis_mem hV' (fun i => stdOrthonormalBasis 𝕜 (V i))
      ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a)
#align direct_sum.is_internal.subordinate_orthonormal_basis_subordinate DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate

end SubordinateOrthonormalBasis

end FiniteDimensional

/-- Given a natural number `n` one less than the `finrank` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`EuclideanSpace 𝕜 (Fin n)`. -/
def OrthonormalBasis.fromOrthogonalSpanSingleton (n : ℕ) [Fact (finrank 𝕜 E = n + 1)] {v : E}
    (hv : v ≠ 0) : OrthonormalBasis (Fin n) 𝕜 (𝕜 ∙ v)ᗮ :=
  -- Porting note: was `attribute [local instance] FiniteDimensional.of_fact_finrank_eq_succ`
  haveI : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ (K := 𝕜) (V := E) n
  (stdOrthonormalBasis _ _).reindex <| finCongr <| finrank_orthogonal_span_singleton hv
#align orthonormal_basis.from_orthogonal_span_singleton OrthonormalBasis.fromOrthogonalSpanSingleton

section LinearIsometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {S : Submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}

open FiniteDimensional

/-- Let `S` be a subspace of a finite-dimensional complex inner product space `V`.  A linear
isometry mapping `S` into `V` can be extended to a full isometry of `V`.

TODO:  The case when `S` is a finite-dimensional subspace of an infinite-dimensional `V`. -/
noncomputable def LinearIsometry.extend (L : S →ₗᵢ[𝕜] V) : V →ₗᵢ[𝕜] V := by
  -- Build an isometry from Sᗮ to L(S)ᗮ through `EuclideanSpace`
  let d := finrank 𝕜 Sᗮ
  let LS := LinearMap.range L.toLinearMap
  have E : Sᗮ ≃ₗᵢ[𝕜] LSᗮ := by
    have dim_LS_perp : finrank 𝕜 LSᗮ = d :=
      calc
        finrank 𝕜 LSᗮ = finrank 𝕜 V - finrank 𝕜 LS := by
          simp only [← LS.finrank_add_finrank_orthogonal, add_tsub_cancel_left]
        _ = finrank 𝕜 V - finrank 𝕜 S := by simp only [LinearMap.finrank_range_of_inj L.injective]
        _ = finrank 𝕜 Sᗮ := by simp only [← S.finrank_add_finrank_orthogonal, add_tsub_cancel_left]

    exact
      (stdOrthonormalBasis 𝕜 Sᗮ).repr.trans
        ((stdOrthonormalBasis 𝕜 LSᗮ).reindex <| finCongr dim_LS_perp).repr.symm
  let L3 := LSᗮ.subtypeₗᵢ.comp E.toLinearIsometry
  -- Project onto S and Sᗮ
  haveI : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  haveI : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  let p1 := (orthogonalProjection S).toLinearMap
  let p2 := (orthogonalProjection Sᗮ).toLinearMap
  -- Build a linear map from the isometries on S and Sᗮ
  let M := L.toLinearMap.comp p1 + L3.toLinearMap.comp p2
  -- Prove that M is an isometry
  have M_norm_map : ∀ x : V, ‖M x‖ = ‖x‖ := by
    intro x
    -- Apply M to the orthogonal decomposition of x
    have Mx_decomp : M x = L (p1 x) + L3 (p2 x) := by
      simp only [M, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearIsometry.coe_toLinearMap]
    -- Mx_decomp is the orthogonal decomposition of M x
    have Mx_orth : ⟪L (p1 x), L3 (p2 x)⟫ = 0 := by
      have Lp1x : L (p1 x) ∈ LinearMap.range L.toLinearMap :=
        LinearMap.mem_range_self L.toLinearMap (p1 x)
      have Lp2x : L3 (p2 x) ∈ (LinearMap.range L.toLinearMap)ᗮ := by
        simp only [LinearIsometry.coe_comp, Function.comp_apply, Submodule.coe_subtypeₗᵢ, ←
          Submodule.range_subtype LSᗮ]
        apply LinearMap.mem_range_self
      apply Submodule.inner_right_of_mem_orthogonal Lp1x Lp2x
    -- Apply the Pythagorean theorem and simplify
    rw [← sq_eq_sq (norm_nonneg _) (norm_nonneg _), norm_sq_eq_add_norm_sq_projection x S]
    simp only [sq, Mx_decomp]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth]
    simp only [p1, p2, LinearIsometry.norm_map, _root_.add_left_inj, mul_eq_mul_left_iff,
      norm_eq_zero, true_or_iff, eq_self_iff_true, ContinuousLinearMap.coe_coe, Submodule.coe_norm,
      Submodule.coe_eq_zero]
  exact
    { toLinearMap := M
      norm_map' := M_norm_map }
#align linear_isometry.extend LinearIsometry.extend

theorem LinearIsometry.extend_apply (L : S →ₗᵢ[𝕜] V) (s : S) : L.extend s = L s := by
  haveI : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  simp only [LinearIsometry.extend, ← LinearIsometry.coe_toLinearMap]
  simp only [add_right_eq_self, LinearIsometry.coe_toLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometry.coe_comp, Function.comp_apply,
    orthogonalProjection_mem_subspace_eq_self, LinearMap.coe_comp, ContinuousLinearMap.coe_coe,
    Submodule.coeSubtype, LinearMap.add_apply, Submodule.coe_eq_zero,
    LinearIsometryEquiv.map_eq_zero_iff, Submodule.coe_subtypeₗᵢ,
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero, Submodule.orthogonal_orthogonal,
    Submodule.coe_mem]
#align linear_isometry.extend_apply LinearIsometry.extend_apply

end LinearIsometry

section Matrix

open Matrix

variable {m n : Type*}

namespace Matrix

variable [Fintype m] [Fintype n] [DecidableEq n]

/-- `Matrix.toLin'` adapted for `EuclideanSpace 𝕜 _`. -/
def toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m :=
  Matrix.toLin' ≪≫ₗ
    LinearEquiv.arrowCongr (WithLp.linearEquiv _ 𝕜 (n → 𝕜)).symm
      (WithLp.linearEquiv _ 𝕜 (m → 𝕜)).symm
#align matrix.to_euclidean_lin Matrix.toEuclideanLin

@[simp]
theorem toEuclideanLin_piLp_equiv_symm (A : Matrix m n 𝕜) (x : n → 𝕜) :
    Matrix.toEuclideanLin A ((WithLp.equiv _ _).symm x) =
      (WithLp.equiv _ _).symm (Matrix.toLin' A x) :=
  rfl
#align matrix.to_euclidean_lin_pi_Lp_equiv_symm Matrix.toEuclideanLin_piLp_equiv_symm

@[simp]
theorem piLp_equiv_toEuclideanLin (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    WithLp.equiv _ _ (Matrix.toEuclideanLin A x) = Matrix.toLin' A (WithLp.equiv _ _ x) :=
  rfl
#align matrix.pi_Lp_equiv_to_euclidean_lin Matrix.piLp_equiv_toEuclideanLin

theorem toEuclideanLin_apply (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin M v = (WithLp.equiv 2 (m → 𝕜)).symm (M *ᵥ (WithLp.equiv 2 (n → 𝕜)) v) :=
  rfl

@[simp]
theorem piLp_equiv_toEuclideanLin_apply (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    WithLp.equiv 2 (m → 𝕜) (toEuclideanLin M v) = M *ᵥ WithLp.equiv 2 (n → 𝕜) v :=
  rfl

@[simp]
theorem toEuclideanLin_apply_piLp_equiv_symm (M : Matrix m n 𝕜) (v : n → 𝕜) :
    toEuclideanLin M ((WithLp.equiv 2 (n→ 𝕜)).symm v) = (WithLp.equiv 2 (m → 𝕜)).symm (M *ᵥ v) :=
  rfl

-- `Matrix.toEuclideanLin` is the same as `Matrix.toLin` applied to `PiLp.basisFun`,
theorem toEuclideanLin_eq_toLin :
    (toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] _) =
      Matrix.toLin (PiLp.basisFun _ _ _) (PiLp.basisFun _ _ _) :=
  rfl
#align matrix.to_euclidean_lin_eq_to_lin Matrix.toEuclideanLin_eq_toLin

open EuclideanSpace in
lemma toEuclideanLin_eq_toLin_orthonormal :
    toEuclideanLin = toLin (basisFun n 𝕜).toBasis (basisFun m 𝕜).toBasis :=
  rfl

end Matrix

local notation "⟪" x ", " y "⟫ₑ" =>
  @inner 𝕜 _ _ (Equiv.symm (WithLp.equiv 2 _) x) (Equiv.symm (WithLp.equiv 2 _) y)

/-- The inner product of a row of `A` and a row of `B` is an entry of `B * Aᴴ`. -/
theorem inner_matrix_row_row [Fintype n] (A B : Matrix m n 𝕜) (i j : m) :
    ⟪A i, B j⟫ₑ = (B * Aᴴ) j i := by
  simp_rw [EuclideanSpace.inner_piLp_equiv_symm, Matrix.mul_apply', Matrix.dotProduct_comm,
    Matrix.conjTranspose_apply, Pi.star_def]
#align inner_matrix_row_row inner_matrix_row_row

/-- The inner product of a column of `A` and a column of `B` is an entry of `Aᴴ * B`. -/
theorem inner_matrix_col_col [Fintype m] (A B : Matrix m n 𝕜) (i j : n) :
    ⟪Aᵀ i, Bᵀ j⟫ₑ = (Aᴴ * B) i j :=
  rfl
#align inner_matrix_col_col inner_matrix_col_col

end Matrix
