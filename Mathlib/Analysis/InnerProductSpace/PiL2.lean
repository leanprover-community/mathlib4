/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Sébastien Gouëzel, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Util.Superscript

/-!
# `L²` inner product space structure on finite products of inner product spaces

The `L²` norm on a finite product of inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \sum \langle x_i, y_i \rangle.
$$
This is recorded in this file as an inner product space instance on `PiLp 2`.

This file develops the notion of a finite-dimensional Hilbert space over `𝕜 = ℂ, ℝ`, referred to as
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
  that it is a finite-dimensional inner product space), and provide a `!ₚ[]` notation (for numeric
  subscripts like `₂`) for the case when the indexing type is `Fin n`.

- `OrthonormalBasis 𝕜 ι`: defined to be an isometry to Euclidean space from a given
  finite-dimensional inner product space, `E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι`.

- `Basis.toOrthonormalBasis`: constructs an `OrthonormalBasis` for a finite-dimensional
  Euclidean space from a `Basis` which is `Orthonormal`.

- `Orthonormal.exists_orthonormalBasis_extension`: provides an existential result of an
  `OrthonormalBasis` extending a given orthonormal set

- `exists_orthonormalBasis`: provides an orthonormal basis on a finite-dimensional vector space

- `stdOrthonormalBasis`: provides an arbitrarily-chosen `OrthonormalBasis` of a given
  finite-dimensional inner product space

- `orthonormalBasisSingleton`: an orthonormal basis formed by a single unit vector in a
  one-dimensional inner product space.

For consequences in infinite dimension (Hilbert bases, etc.), see the file
`Analysis.InnerProductSpace.L2Space`.

-/

@[expose] public section


open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp

noncomputable section

variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [AddCommGroup E] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [AddCommGroup F] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [AddCommGroup F'] [NormedAddCommGroup F'] [InnerProductSpace ℝ F']

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-
If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `PiLp 2 f` for the product space, which is endowed with the `L^2` norm.
-/
instance PiLp.innerProductSpace {ι : Type*} [Fintype ι] (f : ι → Type*) [∀ i, AddCommGroup (f i)]
    [∀ i, NormedAddCommGroup (f i)] [∀ i, InnerProductSpace 𝕜 (f i)] :
    InnerProductSpace 𝕜 (PiLp 2 f) where
  inner x y := ∑ i, ⟪x i, y i⟫
  norm_sq_eq_re_inner x := by
    simp only [PiLp.norm_sq_eq_of_L2, map_sum, ← norm_sq_eq_re_inner]
  conj_inner_symm := by
    intro x y
    unfold inner
    rw [map_sum]
    apply Finset.sum_congr rfl
    rintro z -
    apply inner_conj_symm
  add_left x y z :=
    show (∑ i, ⟪x i + y i, z i⟫ = ∑ i, ⟪x i, z i⟫ + ∑ i, ⟪y i, z i⟫) by
      simp only [inner_add_left, Finset.sum_add_distrib]
  smul_left x y r :=
    show (∑ i : ι, ⟪r • x i, y i⟫ = conj r * ∑ i, ⟪x i, y i⟫) by
      simp only [Finset.mul_sum, inner_smul_left]

theorem PiLp.inner_apply {ι : Type*} [Fintype ι] {f : ι → Type*} [∀ i, AddCommGroup (f i)]
    [∀ i, NormedAddCommGroup (f i)] [∀ i, InnerProductSpace 𝕜 (f i)] (x y : PiLp 2 f) :
    ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
  rfl

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `EuclideanSpace 𝕜 (Fin n)`.

For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building elements of this type,
analogous to `![x, y, ...]` notation. -/
abbrev EuclideanSpace (𝕜 : Type*) (n : Type*) : Type _ :=
  PiLp 2 fun _ : n => 𝕜

section Notation
open Lean Meta Elab Term Macro TSyntax PrettyPrinter.Delaborator SubExpr
open Mathlib.Tactic (subscriptTerm)

/-- Notation for vectors in Lp space. `!₂[x, y, ...]` is a shorthand for
`WithLp.toLp 2 ![x, y, ...]`, of type `EuclideanSpace _ (Fin _)`.

This also works for other subscripts. -/
syntax (name := PiLp.vecNotation) "!" noWs subscriptTerm noWs "[" term,* "]" : term
macro_rules | `(!$p:subscript[$e:term,*]) => do
  -- override the `Fin n.succ` to a literal
  let n := e.getElems.size
  `(WithLp.toLp $p (V := ∀ _ : Fin $(quote n), _) ![$e,*])

/-- Unexpander for the `!₂[x, y, ...]` notation. -/
@[app_delab WithLp.toLp]
meta def EuclideanSpace.delabVecNotation : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 3 do
    -- check that the `WithLp.toLp _` is present
    let p : Term ← withNaryArg 0 <| delab
    -- to be conservative, only allow subscripts which are numerals
    guard <| p matches `($_:num)
    let `(![$elems,*]) := ← withNaryArg 2 delab | failure
    `(!$p[$elems,*])

end Notation

theorem EuclideanSpace.nnnorm_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖₊ = NNReal.sqrt (∑ i, ‖x i‖₊ ^ 2) :=
  PiLp.nnnorm_eq_of_L2 x

theorem EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2) := by
  simpa only [Real.coe_sqrt, NNReal.coe_sum] using congr_arg ((↑) : ℝ≥0 → ℝ) x.nnnorm_eq

theorem EuclideanSpace.norm_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ x

theorem EuclideanSpace.real_norm_sq_eq {n : Type*} [Fintype n] (x : EuclideanSpace ℝ n) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq]

theorem EuclideanSpace.dist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : dist x y = √(∑ i, dist (x i) (y i) ^ 2) :=
  PiLp.dist_eq_of_L2 x y

theorem EuclideanSpace.dist_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2 :=
  PiLp.dist_sq_eq_of_L2 x y

theorem EuclideanSpace.nndist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : nndist x y = NNReal.sqrt (∑ i, nndist (x i) (y i) ^ 2) :=
  PiLp.nndist_eq_of_L2 x y

theorem EuclideanSpace.edist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) :=
  PiLp.edist_eq_of_L2 x y

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
    Real.sqrt_eq_iff_eq_sq this hr]

section

instance EuclideanSpace.infinite [Nonempty ι] : Infinite (EuclideanSpace 𝕜 ι) :=
  Module.Free.infinite 𝕜 _

variable [Fintype ι]

@[simp]
theorem finrank_euclideanSpace :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by
  convert! (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).finrank_eq
  simp

theorem finrank_euclideanSpace_fin {n : ℕ} :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n := by simp

namespace EuclideanSpace

scoped instance (n : ℕ) : Fact (Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem inner_eq_star_dotProduct (x y : EuclideanSpace 𝕜 ι) :
    ⟪x, y⟫ = ofLp y ⬝ᵥ star (ofLp x) := rfl

lemma inner_toLp_toLp (x y : ι → 𝕜) :
    ⟪toLp 2 x, toLp 2 y⟫ = dotProduct y (star x) := rfl

section restrict₂

variable {I J : Finset ι'}

/-- The restriction from `EuclideanSpace 𝕜 J` to `EuclideanSpace 𝕜 I` when `I ⊆ J`. -/
noncomputable
def restrict₂ (hIJ : I ⊆ J) :
    EuclideanSpace 𝕜 J →L[𝕜] EuclideanSpace 𝕜 I where
  toFun x := toLp 2 (Finset.restrict₂ («π» := fun _ ↦ 𝕜) hIJ x.ofLp)
  map_add' x y := by ext; simp
  map_smul' m x := by ext; simp

@[simp]
lemma restrict₂_apply (hIJ : I ⊆ J) (x : EuclideanSpace 𝕜 J) (i : I) :
    EuclideanSpace.restrict₂ hIJ x i = x ⟨i.1, hIJ i.2⟩ := rfl

end restrict₂

end EuclideanSpace

/-- A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce an isometry
from `E` to `PiLp 2` of the subspaces equipped with the `L2` inner product. -/
def DirectSum.IsInternal.isometryL2OfOrthogonalFamily [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : DirectSum.IsInternal V)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    E ≃ₗᵢ[𝕜] PiLp 2 fun i => V i := by
  let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
  let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
  refine LinearEquiv.isometryOfInner ((e₂.symm.trans e₁).trans
    (WithLp.linearEquiv 2 𝕜 (Π i, V i)).symm) ?_
  suffices ∀ (v w : PiLp 2 fun i => V i), ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫ by
    intro v₀ w₀
    simp only [LinearEquiv.trans_apply]
    convert! this (toLp 2 (e₁ (e₂.symm v₀))) (toLp 2 (e₁ (e₂.symm w₀))) <;> simp
  intro v w
  trans ⟪∑ i, (V i).subtypeₗᵢ (v i), ∑ i, (V i).subtypeₗᵢ (w i)⟫
  · simp only [sum_inner, hV'.inner_right_fintype, PiLp.inner_apply]
  · congr <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply [DecidableEq ι]
    {V : ι → Submodule 𝕜 E} (hV : DirectSum.IsInternal V)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (w : PiLp 2 fun i => V i) :
    (hV.isometryL2OfOrthogonalFamily hV').symm w = ∑ i, (w i : E) := by
  classical
    let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
    let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
    suffices ∀ v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i by exact this (e₁.symm w)
    simp [e₁, e₂, DirectSum.coeLinearMap, DirectSum.toModule, DFinsupp.lsum,
      DFinsupp.sumAddHom_apply]

end

variable (ι 𝕜)

/-- A shorthand for `PiLp.continuousLinearEquiv`. -/
abbrev EuclideanSpace.equiv : EuclideanSpace 𝕜 ι ≃L[𝕜] ι → 𝕜 :=
  PiLp.continuousLinearEquiv 2 𝕜 _

variable {ι 𝕜}

/-- The projection on the `i`-th coordinate of `EuclideanSpace 𝕜 ι`, as a linear map. -/
abbrev EuclideanSpace.projₗ (i : ι) : EuclideanSpace 𝕜 ι →ₗ[𝕜] 𝕜 := PiLp.projₗ _ _ i

/-- The projection on the `i`-th coordinate of `EuclideanSpace 𝕜 ι`, as a continuous linear map. -/
abbrev EuclideanSpace.proj (i : ι) : StrongDual 𝕜 (EuclideanSpace 𝕜 ι) := PiLp.proj _ _ i

@[simp]
lemma EuclideanSpace.coe_proj {ι : Type*} (𝕜 : Type*) [RCLike 𝕜] {i : ι} :
    ⇑(@proj ι 𝕜 _ i) = fun x ↦ x i := rfl

section DecEq

variable [DecidableEq ι]

/-- The vector given in Euclidean space by being `a : 𝕜` at coordinate `i : ι` and `0 : 𝕜` at
all other coordinates. -/
abbrev EuclideanSpace.single (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι := PiLp.single 2 i a

@[deprecated PiLp.ofLp_single (since := "2026-03-15")]
lemma EuclideanSpace.ofLp_single (i : ι) (a : 𝕜) : ofLp (single i a) = Pi.single i a := by
  simp

@[deprecated PiLp.toLp_single (since := "2026-03-15")]
lemma EuclideanSpace.toLp_single (i : ι) (a : 𝕜) : toLp _ (Pi.single i a) = single i a := by
  simp

@[deprecated PiLp.single_apply (since := "2026-03-15")]
theorem EuclideanSpace.single_apply (i : ι) (a : 𝕜) (j : ι) :
    (EuclideanSpace.single i a) j = ite (j = i) a 0 := by
  simp

@[deprecated PiLp.single_eq_zero_iff (since := "2026-03-15")]
theorem EuclideanSpace.single_eq_zero_iff {i : ι} {a : 𝕜} :
    EuclideanSpace.single i a = 0 ↔ a = 0 := by simp

variable [Fintype ι]

theorem EuclideanSpace.inner_single_left (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) :
    ⟪EuclideanSpace.single i (a : 𝕜), v⟫ = conj a * v i := by
  simp [PiLp.inner_apply, apply_ite conj, mul_comm]

theorem EuclideanSpace.inner_single_right (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) :
    ⟪v, EuclideanSpace.single i (a : 𝕜)⟫ = a * conj (v i) := by simp [PiLp.inner_apply]

@[deprecated PiLp.norm_single (since := "2026-03-15")]
theorem EuclideanSpace.norm_single (i : ι) (a : 𝕜) :
    ‖EuclideanSpace.single i (a : 𝕜)‖ = ‖a‖ := by simp

@[deprecated PiLp.nnnorm_single (since := "2026-03-15")]
theorem EuclideanSpace.nnnorm_single (i : ι) (a : 𝕜) :
    ‖EuclideanSpace.single i (a : 𝕜)‖₊ = ‖a‖₊ := by simp

@[deprecated PiLp.dist_single_same (since := "2026-03-15")]
theorem EuclideanSpace.dist_single_same (i : ι) (a b : 𝕜) :
    dist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = dist a b := by
  simp

@[deprecated PiLp.nndist_single_same (since := "2026-03-15")]
theorem EuclideanSpace.nndist_single_same (i : ι) (a b : 𝕜) :
    nndist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = nndist a b := by
  simp

@[deprecated PiLp.edist_single_same (since := "2026-03-15")]
theorem EuclideanSpace.edist_single_same (i : ι) (a b : 𝕜) :
    edist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = edist a b := by
  simp

/-- `EuclideanSpace.single` forms an orthonormal family. -/
theorem EuclideanSpace.orthonormal_single :
    Orthonormal 𝕜 fun i : ι => EuclideanSpace.single i (1 : 𝕜) := by
  simp_rw [orthonormal_iff_ite, EuclideanSpace.inner_single_left, map_one, one_mul,
    PiLp.single_apply]
  intros
  trivial

theorem EuclideanSpace.piLpCongrLeft_single
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι) (i' : ι') (v : 𝕜) :
    LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e (EuclideanSpace.single i' v) =
      EuclideanSpace.single (e i') v :=
  LinearIsometryEquiv.piLpCongrLeft_single e i' _

end DecEq

section finAddEquivProd

/-- The canonical linear homeomorphism between `EuclideanSpace 𝕜 (ι ⊕ κ)` and
`EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ`.

See `PiLp.sumPiLpEquivProdLpPiLp` for the isometry version,
where the RHS is equipped with the Euclidean norm rather than the supremum norm. -/
abbrev EuclideanSpace.sumEquivProd {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ] :
    EuclideanSpace 𝕜 (ι ⊕ κ) ≃L[𝕜] EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 _).toContinuousLinearEquiv.trans <|
    WithLp.prodContinuousLinearEquiv _ _ _ _

/-- The canonical linear homeomorphism between `EuclideanSpace 𝕜 (Fin (n + m))` and
`EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)`. -/
abbrev EuclideanSpace.finAddEquivProd {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} :
    EuclideanSpace 𝕜 (Fin (n + m)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv.symm).toContinuousLinearEquiv.trans
    sumEquivProd

end finAddEquivProd

variable (ι 𝕜 E)
variable [Fintype ι]

/-- An orthonormal basis on E is an identification of `E` with its dimensional-matching
`EuclideanSpace 𝕜 ι`. -/
structure OrthonormalBasis where ofRepr ::
  /-- Linear isometry between `E` and `EuclideanSpace 𝕜 ι` representing the orthonormal basis. -/
  repr : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι

variable {ι 𝕜 E}

namespace OrthonormalBasis

theorem repr_injective :
    Injective (repr : OrthonormalBasis ι 𝕜 E → E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) := fun f g h => by
  cases f
  cases g
  congr

/-- `b i` is the `i`th basis vector. -/
instance instFunLike : FunLike (OrthonormalBasis ι 𝕜 E) ι E where
  coe b i := by classical exact b.repr.symm (EuclideanSpace.single i (1 : 𝕜))
  coe_injective' b b' h := repr_injective <| LinearIsometryEquiv.toLinearEquiv_injective <|
    LinearEquiv.symm_bijective.injective <| LinearEquiv.toLinearMap_injective <| by
      classical
        rw [← LinearMap.cancel_right (WithLp.linearEquiv 2 𝕜 (_ → 𝕜)).symm.surjective]
        simp +instances only
        refine LinearMap.pi_ext fun i k => ?_
        have : k = k • (1 : 𝕜) := by rw [smul_eq_mul, mul_one]
        rw [this, Pi.single_smul]
        replace h := congr_fun h i
        simp only [LinearEquiv.comp_coe, map_smul, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
          coe_symm_linearEquiv, PiLp.toLp_single,
          LinearIsometryEquiv.coe_symm_toLinearEquiv] at h ⊢
        rw [h]

@[simp]
theorem coe_ofRepr [DecidableEq ι] (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) :
    ⇑(OrthonormalBasis.ofRepr e) = fun i => e.symm (EuclideanSpace.single i (1 : 𝕜)) := by
  dsimp only [DFunLike.coe]
  funext
  congr!

@[simp]
protected theorem repr_symm_single [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr.symm (EuclideanSpace.single i (1 : 𝕜)) = b i := by
  dsimp only [DFunLike.coe]
  congr!

@[simp]
protected theorem repr_self [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = EuclideanSpace.single i (1 : 𝕜) := by
  rw [← b.repr_symm_single i, LinearIsometryEquiv.apply_symm_apply]

protected theorem repr_apply_apply (b : OrthonormalBasis ι 𝕜 E) (v : E) (i : ι) :
    b.repr v i = ⟪b i, v⟫ := by
  classical
    rw [← b.repr.inner_map_map (b i) v, b.repr_self i, EuclideanSpace.inner_single_left]
    simp only [one_mul, map_one]

@[simp]
protected theorem orthonormal (b : OrthonormalBasis ι 𝕜 E) : Orthonormal 𝕜 b := by
  classical
    rw [orthonormal_iff_ite]
    intro i j
    rw [← b.repr.inner_map_map (b i) (b j), b.repr_self i, b.repr_self j,
      EuclideanSpace.inner_single_left, PiLp.single_apply, map_one, one_mul]

@[simp]
lemma norm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    ‖b i‖ = 1 := b.orthonormal.norm_eq_one i

@[simp]
lemma nnnorm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    ‖b i‖₊ = 1 := b.orthonormal.nnnorm_eq_one i

@[simp]
lemma enorm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    ‖b i‖ₑ = 1 := b.orthonormal.enorm_eq_one i

@[simp]
lemma inner_eq_zero (b : OrthonormalBasis ι 𝕜 E) {i j : ι} (hij : i ≠ j) :
    ⟪b i, b j⟫ = 0 := b.orthonormal.inner_eq_zero hij

lemma inner_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) : ⟪b i, b i⟫ = 1 := by
  simp

lemma inner_eq_ite [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i j : ι) :
    ⟪b i, b j⟫ = if i = j then 1 else 0 := by
  by_cases h : i = j <;> simp [h]

/-- The `Basis ι 𝕜 E` underlying the `OrthonormalBasis` -/
protected def toBasis (b : OrthonormalBasis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.ofEquivFun (b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)))

@[simp]
protected theorem coe_toBasis (b : OrthonormalBasis ι 𝕜 E) : (⇑b.toBasis : ι → E) = ⇑b := rfl

@[simp]
protected theorem coe_toBasis_repr (b : OrthonormalBasis ι 𝕜 E) :
    b.toBasis.equivFun = b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)) :=
  Basis.equivFun_ofEquivFun _

@[simp]
protected theorem coe_toBasis_repr_apply (b : OrthonormalBasis ι 𝕜 E) (x : E) (i : ι) :
    b.toBasis.repr x i = b.repr x i := by
  simp [← Basis.equivFun_apply]

protected theorem sum_repr (b : OrthonormalBasis ι 𝕜 E) (x : E) : ∑ i, b.repr x i • b i = x := by
  simp_rw [← b.coe_toBasis_repr_apply, ← b.coe_toBasis]
  exact b.toBasis.sum_repr x

open scoped InnerProductSpace in
protected theorem sum_repr' (b : OrthonormalBasis ι 𝕜 E) (x : E) : ∑ i, ⟪b i, x⟫_𝕜 • b i = x := by
  nth_rw 2 [← (b.sum_repr x)]
  simp_rw [b.repr_apply_apply x]

protected theorem sum_repr_symm (b : OrthonormalBasis ι 𝕜 E) (v : EuclideanSpace 𝕜 ι) :
    ∑ i, v i • b i = b.repr.symm v := by simpa using (b.toBasis.equivFun_symm_apply v).symm

protected theorem sum_inner_mul_inner (b : OrthonormalBasis ι 𝕜 E) (x y : E) :
    ∑ i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ := by
  have := congr_arg (innerSL 𝕜 x) (b.sum_repr y)
  rw [map_sum] at this
  convert! this
  rw [map_smul, b.repr_apply_apply, mul_comm]
  simp

lemma sum_sq_norm_inner_right (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ∑ i, ‖⟪b i, x⟫‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [@norm_eq_sqrt_re_inner 𝕜, ← OrthonormalBasis.sum_inner_mul_inner b x x, map_sum]
  simp_rw [inner_mul_symm_re_eq_norm, norm_mul, ← inner_conj_symm x, starRingEnd_apply,
    norm_star, ← pow_two]
  rw [Real.sq_sqrt]
  exact Fintype.sum_nonneg fun _ ↦ by positivity

lemma sum_sq_norm_inner_left (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ∑ i, ‖⟪x, b i⟫‖ ^ 2 = ‖x‖ ^ 2 := by
  convert! sum_sq_norm_inner_right b x using 2 with i -
  rw [← inner_conj_symm, RCLike.norm_conj]

open scoped RealInnerProductSpace in
theorem sum_sq_inner_right {E : Type*} [AddCommGroup E] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i : ι, ⟪b i, x⟫ ^ 2 = ‖x‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right]
  simp

open scoped RealInnerProductSpace in
theorem sum_sq_inner_left {ι E : Type*} [AddCommGroup E] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i : ι, ⟪x, b i⟫ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [← b.sum_sq_inner_right, real_inner_comm]

lemma norm_le_card_mul_iSup_norm_inner (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ‖x‖ ≤ √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫‖ := by
  calc ‖x‖
  _ = √(∑ i, ‖⟪b i, x⟫‖ ^ 2) := by rw [sum_sq_norm_inner_right, Real.sqrt_sq (by positivity)]
  _ ≤ √(∑ _ : ι, (⨆ j, ‖⟪b j, x⟫‖) ^ 2) := by
    gcongr with i
    exact le_ciSup (f := fun j ↦ ‖⟪b j, x⟫‖) (by simp) i
  _ = √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫‖ := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_nonneg, Real.sqrt_mul]
    congr
    rw [Real.sqrt_sq]
    cases isEmpty_or_nonempty ι
    · simp
    · exact le_ciSup_of_le (by simp) (Nonempty.some inferInstance) (by positivity)

protected theorem orthogonalProjection_apply_eq_sum {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (b : OrthonormalBasis ι 𝕜 U) (x : E) :
    U.orthogonalProjection x = ∑ i, ⟪(b i : E), x⟫ • b i := by
  simpa only [b.repr_apply_apply, inner_orthogonalProjection_eq_of_mem_left] using
    (b.sum_repr (U.orthogonalProjection x)).symm

@[deprecated (since := "2025-12-31")] alias orthogonalProjection_eq_sum :=
  OrthonormalBasis.orthogonalProjection_apply_eq_sum

protected theorem orthogonalProjection_eq_sum_rankOne {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (b : OrthonormalBasis ι 𝕜 U) :
    U.orthogonalProjection = ∑ i, InnerProductSpace.rankOne 𝕜 (b i) (b i : E) := by
  ext; simp [b.orthogonalProjection_apply_eq_sum]

protected theorem starProjection_eq_sum_rankOne {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (b : OrthonormalBasis ι 𝕜 U) :
    U.starProjection = ∑ i, InnerProductSpace.rankOne 𝕜 (b i : E) (b i : E) := by
  ext; simp [starProjection, b.orthogonalProjection_eq_sum_rankOne]

lemma sum_rankOne_eq_id (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, InnerProductSpace.rankOne 𝕜 (b i) (b i) = .id 𝕜 E := by ext; simp [b.sum_repr']

/-- Mapping an orthonormal basis along a `LinearIsometryEquiv`. -/
protected def map {G : Type*} [AddCommGroup G] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) : OrthonormalBasis ι 𝕜 G where
  repr := L.symm.trans b.repr

@[simp]
protected theorem map_apply {G : Type*} [AddCommGroup G] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) (i : ι) : b.map L i = L (b i) :=
  rfl

@[simp]
protected theorem toBasis_map {G : Type*} [AddCommGroup G] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) :
    (b.map L).toBasis = b.toBasis.map L.toLinearEquiv :=
  rfl

/-- A basis that is orthonormal is an orthonormal basis. -/
def _root_.Module.Basis.toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.ofRepr <|
    LinearEquiv.isometryOfInner (v.equivFun.trans (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).symm)
      (by
        intro x y
        let p : EuclideanSpace 𝕜 ι := toLp 2 (v.equivFun x)
        let q : EuclideanSpace 𝕜 ι := toLp 2 (v.equivFun y)
        have key : ⟪p, q⟫ = ⟪∑ i, p i • v i, ∑ i, q i • v i⟫ := by
          simp [inner_sum, inner_smul_right, hv.inner_left_fintype, PiLp.inner_apply]
        convert! key
        · rw [← v.equivFun.symm_apply_apply x, v.equivFun_symm_apply]
        · rw [← v.equivFun.symm_apply_apply y, v.equivFun_symm_apply])

@[simp]
theorem _root_.Module.Basis.coe_toOrthonormalBasis_repr (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr : E → EuclideanSpace 𝕜 ι) =
    v.equivFun.trans (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).symm :=
  rfl

@[simp]
theorem _root_.Module.Basis.coe_toOrthonormalBasis_repr_symm
    (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr.symm : EuclideanSpace 𝕜 ι → E) =
    (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).trans v.equivFun.symm :=
  rfl

@[simp]
theorem _root_.Module.Basis.toBasis_toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv).toBasis = v := by
  simp only [OrthonormalBasis.toBasis, Basis.toOrthonormalBasis,
    LinearEquiv.isometryOfInner_toLinearEquiv]
  exact v.ofEquivFun_equivFun

@[simp]
theorem _root_.Module.Basis.coe_toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv : ι → E) = (v : ι → E) :=
  calc
    (v.toOrthonormalBasis hv : ι → E) = ((v.toOrthonormalBasis hv).toBasis : ι → E) := by
      classical rw [OrthonormalBasis.coe_toBasis]
    _ = (v : ι → E) := by simp

section Singleton
variable {ι 𝕜 : Type*} [Unique ι] [RCLike 𝕜]

variable (ι 𝕜) in
/-- `OrthonormalBasis.singleton ι 𝕜` is the orthonormal basis sending the unique element of `ι` to
`1 : 𝕜`. -/
protected noncomputable def singleton : OrthonormalBasis ι 𝕜 𝕜 :=
  (Basis.singleton ι 𝕜).toOrthonormalBasis (by simp)

@[simp]
theorem singleton_apply (i) : OrthonormalBasis.singleton ι 𝕜 i = 1 := Basis.singleton_apply _ _ _

@[simp]
theorem singleton_repr (x i) : (OrthonormalBasis.singleton ι 𝕜).repr x i = x :=
  Basis.singleton_repr _ _ _ _

@[simp]
theorem coe_singleton : ⇑(OrthonormalBasis.singleton ι 𝕜) = 1 := by
  ext; simp

@[simp]
theorem toBasis_singleton : (OrthonormalBasis.singleton ι 𝕜).toBasis = Basis.singleton ι 𝕜 :=
  Basis.toBasis_toOrthonormalBasis _ _

end Singleton

/-- `Pi.orthonormalBasis (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i))` is the
`Σ i, ι i`-indexed orthonormal basis on `Π i, E i` given by `B i` on each component. -/
protected def _root_.Pi.orthonormalBasis {η : Type*} [Fintype η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i)) :
    OrthonormalBasis ((i : η) × ι i) 𝕜 (PiLp 2 E) where
  repr := .trans
      (.piLpCongrRight 2 fun i => (B i).repr)
      (.symm <| .piLpCurry 𝕜 2 fun _ _ => 𝕜)

theorem _root_.Pi.orthonormalBasis.toBasis {η : Type*} [Fintype η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i)) :
    (Pi.orthonormalBasis B).toBasis =
      ((Pi.basis fun i : η ↦ (B i).toBasis).map (WithLp.linearEquiv 2 _ _).symm) := by ext; rfl

@[simp]
theorem _root_.Pi.orthonormalBasis_apply {η : Type*} [Fintype η] [DecidableEq η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i))
    (j : (i : η) × (ι i)) :
    Pi.orthonormalBasis B j = PiLp.single 2 j.fst (B j.fst j.snd) := by
  classical
  ext k
  obtain ⟨i, j⟩ := j
  simp only [Pi.orthonormalBasis, coe_ofRepr, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.piLpCongrRight_symm,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrRight_apply,
    LinearIsometryEquiv.piLpCurry_apply, PiLp.ofLp_single, PiLp.toLp_apply,
    Sigma.curry_single (γ := fun _ _ => 𝕜)]
  obtain rfl | hi := Decidable.eq_or_ne i k
  · simp
  · simp [hi]

@[simp]
theorem _root_.Pi.orthonormalBasis_repr {η : Type*} [Fintype η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, AddCommGroup (E i)]
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i)) (x : (i : η) → E i)
    (j : (i : η) × (ι i)) :
    (Pi.orthonormalBasis B).repr (toLp 2 x) j = (B j.fst).repr (x j.fst) j.snd := rfl

variable {v : ι → E}

/-- A finite orthonormal set that spans is an orthonormal basis -/
protected def mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)) :
    OrthonormalBasis ι 𝕜 E :=
  (Basis.mk (Orthonormal.linearIndependent hon) hsp).toOrthonormalBasis (by rwa [Basis.coe_mk])

@[simp]
protected theorem coe_mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)) :
    ⇑(OrthonormalBasis.mk hon hsp) = v := by
  classical rw [OrthonormalBasis.mk, _root_.Module.Basis.coe_toOrthonormalBasis, Basis.coe_mk]

/-- Any finite subset of an orthonormal family is an `OrthonormalBasis` for its span. -/
protected def span [DecidableEq E] {v' : ι' → E} (h : Orthonormal 𝕜 v') (s : Finset ι') :
    OrthonormalBasis s 𝕜 (span 𝕜 (s.image v' : Set E)) :=
  let e₀' : Basis s 𝕜 _ :=
    Basis.span (h.linearIndependent.comp ((↑) : s → ι') Subtype.val_injective)
  let e₀ : OrthonormalBasis s 𝕜 _ :=
    OrthonormalBasis.mk
      (by
        convert! orthonormal_span (h.comp ((↑) : s → ι') Subtype.val_injective)
        simp [e₀', Basis.span_apply])
      e₀'.span_eq.ge
  let φ : span 𝕜 (s.image v' : Set E) ≃ₗᵢ[𝕜] span 𝕜 (range (v' ∘ ((↑) : s → ι'))) :=
    LinearIsometryEquiv.ofEq _ _
      (by
        rw [Finset.coe_image, image_eq_range]
        rfl)
  e₀.map φ.symm

@[simp]
protected theorem span_apply [DecidableEq E] {v' : ι' → E} (h : Orthonormal 𝕜 v') (s : Finset ι')
    (i : s) : (OrthonormalBasis.span h s i : E) = v' i := by
  simp only [OrthonormalBasis.span, Basis.span_apply, LinearIsometryEquiv.ofEq_symm,
    OrthonormalBasis.map_apply, OrthonormalBasis.coe_mk, LinearIsometryEquiv.coe_ofEq_apply,
    comp_apply]

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

@[simp]
protected theorem coe_of_orthogonal_eq_bot_mk (hon : Orthonormal 𝕜 v)
    (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) : ⇑(OrthonormalBasis.mkOfOrthogonalEqBot hon hsp) = v :=
  OrthonormalBasis.coe_mk hon _

variable [Fintype ι']

/-- `b.reindex (e : ι ≃ ι')` is an `OrthonormalBasis` indexed by `ι'` -/
def reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') : OrthonormalBasis ι' 𝕜 E :=
  OrthonormalBasis.ofRepr (b.repr.trans (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e))

protected theorem reindex_apply (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
    (b.reindex e) i' = b (e.symm i') := by
  classical
    dsimp [reindex]
    rw [coe_ofRepr]
    dsimp
    rw [← b.repr_symm_single, LinearIsometryEquiv.piLpCongrLeft_symm,
      EuclideanSpace.piLpCongrLeft_single]

@[simp]
theorem reindex_toBasis (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') :
    (b.reindex e).toBasis = b.toBasis.reindex e := Basis.eq_ofRepr_eq_repr fun _ ↦ congr_fun rfl

@[simp]
protected theorem coe_reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⇑(b.reindex e) = b ∘ e.symm :=
  funext (b.reindex_apply e)

@[simp]
protected theorem repr_reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (x : E) (i' : ι') :
    (b.reindex e).repr x i' = b.repr x (e.symm i') := by
  classical
  rw [OrthonormalBasis.repr_apply_apply, b.repr_apply_apply, OrthonormalBasis.coe_reindex,
    comp_apply]

end OrthonormalBasis

namespace EuclideanSpace

variable (𝕜 ι)

/-- The basis `Pi.basisFun`, bundled as an orthonormal basis of `EuclideanSpace 𝕜 ι`. -/
noncomputable def basisFun : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι) :=
  ⟨LinearIsometryEquiv.refl _ _⟩

@[simp]
theorem basisFun_apply [DecidableEq ι] (i : ι) : basisFun ι 𝕜 i = EuclideanSpace.single i 1 :=
  PiLp.basisFun_apply _ _ _ _

@[simp]
theorem basisFun_repr (x : EuclideanSpace 𝕜 ι) (i : ι) : (basisFun ι 𝕜).repr x i = x i := rfl

@[simp]
theorem basisFun_inner (x : EuclideanSpace 𝕜 ι) (i : ι) : ⟪basisFun ι 𝕜 i, x⟫ = x i := by
  simp [← OrthonormalBasis.repr_apply_apply]

@[simp]
theorem inner_basisFun_real (x : EuclideanSpace ℝ ι) (i : ι) :
    inner ℝ x (basisFun ι ℝ i) = x i := by
  rw [real_inner_comm, basisFun_inner]

theorem basisFun_toBasis : (basisFun ι 𝕜).toBasis = PiLp.basisFun _ 𝕜 ι := rfl

end EuclideanSpace

instance OrthonormalBasis.instInhabited : Inhabited (OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) :=
  ⟨EuclideanSpace.basisFun ι 𝕜⟩

namespace OrthonormalBasis

variable {E' : Type*} [Fintype ι'] [AddCommGroup E'] [NormedAddCommGroup E']
  [InnerProductSpace 𝕜 E'] (b : OrthonormalBasis ι 𝕜 E) (b' : OrthonormalBasis ι' 𝕜 E') (e : ι ≃ ι')

/-- The `LinearIsometryEquiv` which maps an orthonormal basis to another. This is a convenience
wrapper around `Orthonormal.equiv`. -/
protected def equiv : E ≃ₗᵢ[𝕜] E' :=
  b.repr.trans <| .trans (.piLpCongrLeft _ _ _ e) b'.repr.symm

@[simp]
lemma equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm := by
  apply b'.toBasis.ext_linearIsometryEquiv
  simp [OrthonormalBasis.equiv]

@[simp]
lemma equiv_apply_basis (i : ι) : b.equiv b' e (b i) = b' (e i) := by
  classical
  simp only [OrthonormalBasis.equiv, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self]
  refine DFunLike.congr rfl ?_
  ext j
  simp

@[simp]
lemma equiv_self_rfl : b.equiv b (.refl ι) = .refl 𝕜 E := by
  apply b.toBasis.ext_linearIsometryEquiv
  simp

lemma equiv_apply (x : E) : b.equiv b' e x = ∑ i, b.repr x i • b' (e i) := by
  nth_rw 1 [← b.sum_repr x, map_sum]
  simp_rw [map_smul, equiv_apply_basis]

lemma equiv_apply_euclideanSpace (x : EuclideanSpace 𝕜 ι) :
    (EuclideanSpace.basisFun ι 𝕜).equiv b (Equiv.refl ι) x = ∑ i, x i • b i := by
  simp_rw [equiv_apply, EuclideanSpace.basisFun_repr, Equiv.refl_apply]

lemma coe_equiv_euclideanSpace :
    ⇑((EuclideanSpace.basisFun ι 𝕜).equiv b (Equiv.refl ι)) = fun x ↦ ∑ i, x i • b i := by
  simp_rw [← equiv_apply_euclideanSpace]

end OrthonormalBasis

section Complex

/-- `![1, I]` is an orthonormal basis for `ℂ` considered as a real inner product space. -/
def Complex.orthonormalBasisOneI : OrthonormalBasis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.toOrthonormalBasis
    (by
      rw [orthonormal_iff_ite]
      intro i; fin_cases i <;> intro j <;> fin_cases j <;> simp [real_inner_eq_re_inner])

@[simp]
theorem Complex.orthonormalBasisOneI_repr_apply (z : ℂ) :
    Complex.orthonormalBasisOneI.repr z = ![z.re, z.im] :=
  rfl

@[simp]
theorem Complex.orthonormalBasisOneI_repr_symm_apply (x : EuclideanSpace ℝ (Fin 2)) :
    Complex.orthonormalBasisOneI.repr.symm x = x 0 + x 1 * I :=
  rfl

@[simp]
theorem Complex.toBasis_orthonormalBasisOneI :
    Complex.orthonormalBasisOneI.toBasis = Complex.basisOneI :=
  Basis.toBasis_toOrthonormalBasis _ _

@[simp]
theorem Complex.coe_orthonormalBasisOneI :
    (Complex.orthonormalBasisOneI : Fin 2 → ℂ) = ![1, I] := by
  simp [Complex.orthonormalBasisOneI]

/-- The isometry between `ℂ` and a two-dimensional real inner product space given by a basis. -/
def Complex.isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) ℝ F) : ℂ ≃ₗᵢ[ℝ] F :=
  Complex.orthonormalBasisOneI.repr.trans v.repr.symm

@[simp]
theorem Complex.map_isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) ℝ F) (f : F ≃ₗᵢ[ℝ] F') :
    Complex.isometryOfOrthonormal (v.map f) = (Complex.isometryOfOrthonormal v).trans f := by
  simp only [isometryOfOrthonormal, OrthonormalBasis.map, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm]
  -- Porting note: `LinearIsometryEquiv.trans_assoc` doesn't trigger in the `simp` above
  rw [LinearIsometryEquiv.trans_assoc]

theorem Complex.isometryOfOrthonormal_symm_apply (v : OrthonormalBasis (Fin 2) ℝ F) (f : F) :
    (Complex.isometryOfOrthonormal v).symm f =
      (v.toBasis.coord 0 f : ℂ) + (v.toBasis.coord 1 f : ℂ) * I := by
  simp [Complex.isometryOfOrthonormal]

theorem Complex.isometryOfOrthonormal_apply (v : OrthonormalBasis (Fin 2) ℝ F) (z : ℂ) :
    Complex.isometryOfOrthonormal v z = z.re • v 0 + z.im • v 1 := by
  simp [Complex.isometryOfOrthonormal, ← v.sum_repr_symm]

end Complex

open Module

/-! ### Matrix representation of an orthonormal basis with respect to another -/


section ToMatrix

variable [DecidableEq ι]

section
open scoped Matrix

/-- A version of `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` that works for bases with
different index types. -/
@[simp]
theorem OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self [Fintype ι']
    (a : OrthonormalBasis ι' 𝕜 E) (b : OrthonormalBasis ι 𝕜 E) :
    (a.toBasis.toMatrix b)ᴴ * a.toBasis.toMatrix b = 1 := by
  ext i j
  convert! a.repr.inner_map_map (b i) (b j)
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_def, PiLp.inner_apply,
      inner_apply']
    congr
  · rw [orthonormal_iff_ite.mp b.orthonormal i j, Matrix.one_apply]

/-- A version of `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` that works for bases with
different index types. -/
@[simp]
theorem OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose [Fintype ι']
    (a : OrthonormalBasis ι 𝕜 E) (b : OrthonormalBasis ι' 𝕜 E) :
    a.toBasis.toMatrix b * (a.toBasis.toMatrix b)ᴴ = 1 := by
  classical
  rw [Matrix.mul_eq_one_comm_of_equiv (a.toBasis.indexEquiv b.toBasis),
    a.toMatrix_orthonormalBasis_conjTranspose_mul_self b]

variable (a b : OrthonormalBasis ι 𝕜 E)

/-- The change-of-basis matrix between two orthonormal bases `a`, `b` is a unitary matrix. -/
theorem OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary :
    a.toBasis.toMatrix b ∈ Matrix.unitaryGroup ι 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact a.toMatrix_orthonormalBasis_conjTranspose_mul_self b

/-- The determinant of the change-of-basis matrix between two orthonormal bases `a`, `b` has
unit length. -/
@[simp]
theorem OrthonormalBasis.det_to_matrix_orthonormalBasis : ‖a.toBasis.det b‖ = 1 := by
  have := (Matrix.det_of_mem_unitary (a.toMatrix_orthonormalBasis_mem_unitary b)).2
  rw [star_def, RCLike.mul_conj] at this
  norm_cast at this
  rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at this

end

section Real

variable (a b : OrthonormalBasis ι ℝ F)

/-- The change-of-basis matrix between two orthonormal bases `a`, `b` is an orthogonal matrix. -/
theorem OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal :
    a.toBasis.toMatrix b ∈ Matrix.orthogonalGroup ι ℝ :=
  a.toMatrix_orthonormalBasis_mem_unitary b

/-- The determinant of the change-of-basis matrix between two orthonormal bases `a`, `b` is ±1. -/
theorem OrthonormalBasis.det_to_matrix_orthonormalBasis_real :
    a.toBasis.det b = 1 ∨ a.toBasis.det b = -1 := by
  rw [← sq_eq_one_iff]
  simpa [unitary, sq] using Matrix.det_of_mem_unitary (a.toMatrix_orthonormalBasis_mem_unitary b)

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
    (v_family : ∀ i, OrthonormalBasis (α i) 𝕜 (A i)) : OrthonormalBasis (Σ i, α i) 𝕜 E :=
  (hV_sum.collectedBasis fun i => (v_family i).toBasis).toOrthonormalBasis <| by
    simpa using
      hV.orthonormal_sigma_orthonormal (show ∀ i, Orthonormal 𝕜 (v_family i).toBasis by simp)

theorem DirectSum.IsInternal.collectedOrthonormalBasis_mem [DecidableEq ι]
    (h : DirectSum.IsInternal A) {α : ι → Type*} [∀ i, Fintype (α i)]
    (hV : OrthogonalFamily 𝕜 (fun i => A i) fun i => (A i).subtypeₗᵢ)
    (v : ∀ i, OrthonormalBasis (α i) 𝕜 (A i)) (a : Σ i, α i) :
    h.collectedOrthonormalBasis hV v a ∈ A a.1 := by
  simp [DirectSum.IsInternal.collectedOrthonormalBasis]

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

theorem Orthonormal.exists_orthonormalBasis_extension_of_card_eq {ι : Type*} [Fintype ι]
    (card_ι : finrank 𝕜 E = Fintype.card ι) {v : ι → E} {s : Set ι}
    (hv : Orthonormal 𝕜 (s.restrict v)) : ∃ b : OrthonormalBasis ι 𝕜 E, ∀ i ∈ s, b i = v i := by
  have hsv : Injective (s.restrict v) := hv.linearIndependent.injective
  have hX : Orthonormal 𝕜 ((↑) : Set.range (s.restrict v) → E) := by
    rwa [orthonormal_subtype_range hsv]
  obtain ⟨Y, b₀, hX, hb₀⟩ := hX.exists_orthonormalBasis_extension
  have hιY : Fintype.card ι = Y.card := by
    refine card_ι.symm.trans ?_
    exact Module.finrank_eq_card_finset_basis b₀.toBasis
  have hvsY : s.MapsTo v Y := (s.mapsTo_image v).mono_right (by rwa [← range_restrict])
  have hsv' : Set.InjOn v s := by
    rw [Set.injOn_iff_injective]
    exact hsv
  obtain ⟨g, hg⟩ := hvsY.exists_equiv_extend_of_card_eq hιY hsv'
  use b₀.reindex g.symm
  intro i hi
  simp [hb₀, hg i hi]

variable (𝕜 E)

/-- A finite-dimensional inner product space admits an orthonormal basis. -/
theorem _root_.exists_orthonormalBasis :
    ∃ (w : Finset E) (b : OrthonormalBasis w 𝕜 E), ⇑b = ((↑) : w → E) :=
  let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_orthonormalBasis_extension
  ⟨w, hw, hw''⟩

/-- A finite-dimensional `InnerProductSpace` has an orthonormal basis. -/
irreducible_def stdOrthonormalBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E := by
  let b := Classical.choose (Classical.choose_spec <| exists_orthonormalBasis 𝕜 E)
  rw [finrank_eq_card_basis b.toBasis]
  exact b.reindex (Fintype.equivFinOfCardEq rfl)

/-- An orthonormal basis of `ℝ` is made either of the vector `1`, or of the vector `-1`. -/
theorem orthonormalBasis_one_dim (b : OrthonormalBasis ι ℝ ℝ) :
    (⇑b = fun _ => (1 : ℝ)) ∨ ⇑b = fun _ => (-1 : ℝ) := by
  have : Unique ι := b.toBasis.unique
  have : b default = 1 ∨ b default = -1 := by
    have : ‖b default‖ = 1 := b.orthonormal.1 _
    rwa [Real.norm_eq_abs, abs_eq (zero_le_one' ℝ)] at this
  rw [eq_const_of_unique b]
  grind

variable {𝕜 E}

section SubordinateOrthonormalBasis

open DirectSum

variable {n : ℕ} (hn : finrank 𝕜 E = n) [DecidableEq ι] {V : ι → Submodule 𝕜 E} (hV : IsInternal V)

/-- Exhibit a bijection between `Fin n` and the index set of a certain basis of an `n`-dimensional
inner product space `E`.  This should not be accessed directly, but only via the subsequent API. -/
irreducible_def DirectSum.IsInternal.sigmaOrthonormalBasisIndexEquiv
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    (Σ i, Fin (finrank 𝕜 (V i))) ≃ Fin n :=
  let b := hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)
  Fintype.equivFinOfCardEq <| (Module.finrank_eq_card_basis b.toBasis).symm.trans hn

/-- An `n`-dimensional `InnerProductSpace` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `Fin n` and subordinate to that direct sum. -/
irreducible_def DirectSum.IsInternal.subordinateOrthonormalBasis
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    OrthonormalBasis (Fin n) 𝕜 E :=
  (hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)).reindex
    (hV.sigmaOrthonormalBasisIndexEquiv hn hV')

/-- An `n`-dimensional `InnerProductSpace` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `Fin n` and subordinate to that direct sum. This function
provides the mapping by which it is subordinate. -/
irreducible_def DirectSum.IsInternal.subordinateOrthonormalBasisIndex (a : Fin n)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) : ι :=
  ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a).1

/-- The basis constructed in `DirectSum.IsInternal.subordinateOrthonormalBasis` is subordinate to
the `OrthogonalFamily` in question. -/
theorem DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate (a : Fin n)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    hV.subordinateOrthonormalBasis hn hV' a ∈ V (hV.subordinateOrthonormalBasisIndex hn a hV') := by
  simpa only [DirectSum.IsInternal.subordinateOrthonormalBasis, OrthonormalBasis.coe_reindex,
    DirectSum.IsInternal.subordinateOrthonormalBasisIndex] using
    hV.collectedOrthonormalBasis_mem hV' (fun i => stdOrthonormalBasis 𝕜 (V i))
      ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a)

theorem DirectSum.IsInternal.exists_subordinateOrthonormalBasisIndex_eq
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) {i : ι} (hi : V i ≠ ⊥) :
    ∃ a : Fin n, hV.subordinateOrthonormalBasisIndex hn a hV' = i := by
  use hV.sigmaOrthonormalBasisIndexEquiv hn hV' ⟨i, ⟨0, by grind [finrank_eq_zero (S := V i)]⟩⟩
  simp [subordinateOrthonormalBasisIndex_def]

private def DirectSum.IsInternal.subordinateOrthonormalBasisIndexFiberEquiv
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (i : ι) :
    {a : Fin n // hV.subordinateOrthonormalBasisIndex hn a hV' = i} ≃ Fin (finrank 𝕜 (V i)) where
  toFun a := Fin.cast (by rw [← subordinateOrthonormalBasisIndex_def, a.property])
    ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a).snd
  invFun b := ⟨hV.sigmaOrthonormalBasisIndexEquiv hn hV' ⟨i, b⟩,
    by simp [subordinateOrthonormalBasisIndex_def]⟩
  left_inv := by grind [subordinateOrthonormalBasisIndex_def, Fin.cast_eq_self]
  right_inv := by grind

theorem DirectSum.IsInternal.card_filter_subordinateOrthonormalBasisIndex_eq
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (i : ι) :
    Finset.card {a | hV.subordinateOrthonormalBasisIndex hn a hV' = i} = finrank 𝕜 (V i) := by
  apply Finset.card_eq_of_equiv_fin
  simpa using hV.subordinateOrthonormalBasisIndexFiberEquiv hn hV' i

end SubordinateOrthonormalBasis

end FiniteDimensional

/-- Given a natural number `n` one less than the `finrank` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`EuclideanSpace 𝕜 (Fin n)`. -/
def OrthonormalBasis.fromOrthogonalSpanSingleton (n : ℕ) [Fact (finrank 𝕜 E = n + 1)] {v : E}
    (hv : v ≠ 0) : OrthonormalBasis (Fin n) 𝕜 (𝕜 ∙ v)ᗮ :=
  have : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ (K := 𝕜) (V := E) n
  (stdOrthonormalBasis _ _).reindex <| finCongr <| finrank_orthogonal_span_singleton hv

section LinearIsometry

variable {V : Type*} [AddCommGroup V] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]
variable {S : Submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}

open Module

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
        _ = finrank 𝕜 V - finrank 𝕜 S := by
          simp only [LS, LinearMap.finrank_range_of_inj L.injective]
        _ = finrank 𝕜 Sᗮ := by simp only [← S.finrank_add_finrank_orthogonal, add_tsub_cancel_left]
    exact
      (stdOrthonormalBasis 𝕜 Sᗮ).repr.trans
        ((stdOrthonormalBasis 𝕜 LSᗮ).reindex <| finCongr dim_LS_perp).repr.symm
  let L3 := LSᗮ.subtypeₗᵢ.comp E.toLinearIsometry
  -- Project onto S and Sᗮ
  haveI : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  haveI : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  let p1 := S.orthogonalProjection.toLinearMap
  let p2 := Sᗮ.orthogonalProjection.toLinearMap
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
        simp only [LS,
          ← Submodule.range_subtype LSᗮ]
        apply LinearMap.mem_range_self
      apply Submodule.inner_right_of_mem_orthogonal Lp1x Lp2x
    -- Apply the Pythagorean theorem and simplify
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_add_norm_sq_projection x S]
    simp only [sq, Mx_decomp]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth]
    simp only [p1, p2, LinearIsometry.norm_map,
      ContinuousLinearMap.coe_coe, Submodule.coe_norm]
  exact
    { toLinearMap := M
      norm_map' := M_norm_map }

theorem LinearIsometry.extend_apply (L : S →ₗᵢ[𝕜] V) (s : S) : L.extend s = L s := by
  simp only [LinearIsometry.extend, ← LinearIsometry.coe_toLinearMap]
  simp only [add_eq_left, LinearIsometry.coe_toLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometry.coe_comp, Function.comp_apply,
    orthogonalProjection_mem_subspace_eq_self, LinearMap.coe_comp, ContinuousLinearMap.coe_coe,
    Submodule.coe_subtype, LinearMap.add_apply, Submodule.coe_eq_zero,
    LinearIsometryEquiv.map_eq_zero_iff, Submodule.coe_subtypeₗᵢ,
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero, Submodule.orthogonal_orthogonal,
    Submodule.coe_mem]

end LinearIsometry

section Matrix

open Matrix

variable {m n : Type*}

namespace Matrix

variable [Fintype n] [DecidableEq n]

/-- A shorthand for `Matrix.toLpLin 2 2`. -/
abbrev toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m :=
  toLpLin 2 2

@[deprecated toLpLin_toLp (since := "2026-01-22")]
lemma toEuclideanLin_toLp (A : Matrix m n 𝕜) (x : n → 𝕜) :
    Matrix.toEuclideanLin A (toLp _ x) = toLp _ (Matrix.toLin' A x) := rfl

@[deprecated ofLp_toLpLin (since := "2026-01-22")]
theorem piLp_ofLp_toEuclideanLin (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ofLp (Matrix.toEuclideanLin A x) = Matrix.toLin' A (ofLp x) :=
  rfl

@[deprecated toLpLin_apply (since := "2026-01-22")]
theorem toEuclideanLin_apply (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin M v = toLp _ (M *ᵥ ofLp v) := rfl

@[deprecated ofLp_toLpLin (since := "2026-01-22")]
theorem ofLp_toEuclideanLin_apply (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    ofLp (toEuclideanLin M v) = M *ᵥ ofLp v :=
  rfl

@[deprecated toLpLin_toLp (since := "2026-01-22")]
theorem toEuclideanLin_apply_piLp_toLp (M : Matrix m n 𝕜) (v : n → 𝕜) :
    toEuclideanLin M (toLp _ v) = toLp _ (M *ᵥ v) :=
  rfl

-- `Matrix.toEuclideanLin` is the same as `Matrix.toLin` applied to `PiLp.basisFun`,
@[deprecated toLpLin_eq_toLin (since := "2026-01-22")]
theorem toEuclideanLin_eq_toLin [Finite m] :
    (toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] _) =
      Matrix.toLin (PiLp.basisFun _ _ _) (PiLp.basisFun _ _ _) :=
  rfl

open EuclideanSpace in
lemma toEuclideanLin_eq_toLin_orthonormal [Fintype m] :
    toEuclideanLin = toLin (basisFun n 𝕜).toBasis (basisFun m 𝕜).toBasis :=
  rfl

end Matrix

local notation "⟪" x ", " y "⟫ₑ" => inner 𝕜 (toLp 2 x) (toLp 2 y)

/-- The inner product of a row of `A` and a row of `B` is an entry of `B * Aᴴ`. -/
theorem inner_matrix_row_row [Fintype n] (A B : Matrix m n 𝕜) (i j : m) :
    ⟪A i, B j⟫ₑ = (B * Aᴴ) j i := by
  simp [PiLp.inner_apply, dotProduct, mul_apply']

/-- The inner product of a column of `A` and a column of `B` is an entry of `Aᴴ * B`. -/
theorem inner_matrix_col_col [Fintype m] (A B : Matrix m n 𝕜) (i j : n) :
    ⟪Aᵀ i, Bᵀ j⟫ₑ = (Aᴴ * B) i j := by
  simp [PiLp.inner_apply, dotProduct, mul_apply', mul_comm]

/-- The matrix representation of `innerSL 𝕜 x` given by an orthonormal basis `b` and `b₂`
is equal to `vecMulVec (star b₂) (star (b.repr x))`. -/
theorem LinearMap.toMatrix_innerₛₗ_apply [Fintype n] [DecidableEq n] [Fintype m]
    (b : OrthonormalBasis n 𝕜 E) (b₂ : OrthonormalBasis m 𝕜 𝕜) (x : E) :
    (innerₛₗ 𝕜 x).toMatrix b.toBasis b₂.toBasis = vecMulVec (star b₂) (star (b.repr x)) := by
  ext; simp [LinearMap.toMatrix_apply, vecMulVec_apply, OrthonormalBasis.repr_apply_apply, mul_comm]

@[deprecated (since := "2026-01-03")] alias toMatrix_innerSL_apply :=
  LinearMap.toMatrix_innerₛₗ_apply

end Matrix

open ContinuousLinearMap LinearMap in
theorem InnerProductSpace.toMatrix_rankOne {𝕜 E F ι ι' : Type*} [RCLike 𝕜] [AddCommGroup E]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [AddCommGroup F] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F]
    [Finite ι] [Fintype ι'] [DecidableEq ι'] (x : E) (y : F) (b : Module.Basis ι 𝕜 E)
    (b' : OrthonormalBasis ι' 𝕜 F) :
    (rankOne 𝕜 x y).toMatrix b'.toBasis b = .vecMulVec (b.repr x) (star (b'.repr y)) := by
  have := Fintype.ofFinite ι
  rw [rankOne_def', ContinuousLinearMap.coe_comp, toLinearMap_toSpanSingleton,
    toMatrix_comp _ (OrthonormalBasis.singleton Unit 𝕜).toBasis, toMatrix_toSpanSingleton,
    toLinearMap_innerSL_apply, toMatrix_innerₛₗ_apply, OrthonormalBasis.toBasis_singleton,
    Basis.coe_singleton, Matrix.vecMulVec_one, OrthonormalBasis.coe_singleton, star_one,
    Matrix.one_vecMulVec, Matrix.vecMulVec_eq Unit]

open Matrix LinearMap EuclideanSpace in
theorem InnerProductSpace.symm_toEuclideanLin_rankOne {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m]
    [Fintype n] [DecidableEq n] (x : EuclideanSpace 𝕜 m) (y : EuclideanSpace 𝕜 n) :
    toEuclideanLin.symm (rankOne 𝕜 x y) = .vecMulVec x (star y) := by
  simp [toLpLin, toMatrix', ← ext_iff, vecMulVec_apply, inner_single_right, mul_comm]

namespace FiniteDimensional
variable [Unique ι] (h : Module.finrank 𝕜 E = 1) {v : E} (hv : ‖v‖ = 1)

variable (ι 𝕜 v) in
/-- In an inner product space with dimension 1, a set `{v}` is an orthonormal basis for
`‖v‖ = 1`. -/
def orthonormalBasisSingleton : OrthonormalBasis ι 𝕜 E :=
  (basisSingleton ι h v (by aesop)).toOrthonormalBasis (by simpa)

@[simp]
theorem orthonormalBasisSingleton_apply (i : ι) :
   orthonormalBasisSingleton ι 𝕜 h v hv i = v := by
  simp [orthonormalBasisSingleton]

@[simp]
theorem toBasis_orthonormalBasisSingleton :
    (orthonormalBasisSingleton ι 𝕜 h v hv).toBasis = basisSingleton ι h v (by aesop) := by
  simp [orthonormalBasisSingleton]

@[simp]
theorem orthonormalBasisSingleton_repr_apply (w : E) :
    (orthonormalBasisSingleton ι 𝕜 h v hv).repr w = .single default ⟪v, w⟫ := by
  ext
  simp [OrthonormalBasis.repr_apply_apply, Unique.eq_default]

theorem range_orthonormalBasisSingleton :
    Set.range (orthonormalBasisSingleton ι 𝕜 h v hv) = {v} := by
  simp

end FiniteDimensional
