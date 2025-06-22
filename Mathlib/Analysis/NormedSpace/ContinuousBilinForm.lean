import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Continuous bilinear forms
-/

open scoped Matrix

namespace ContinuousBilinForm

variable {𝕜 E n : Type*} [SeminormedAddCommGroup E]

section RCLike

variable [RCLike 𝕜] [NormedSpace 𝕜 E]

variable (𝕜 E) in
/- The type of continuous bilinear forms. -/
abbrev _root_.ContinuousBilinForm := E →L[𝕜] E →L[𝕜] 𝕜

variable (f : ContinuousBilinForm 𝕜 E) (b : Basis n 𝕜 E)

/-- The underlying bilinear form of a continuous bilinear form -/
def toBilinForm : LinearMap.BilinForm 𝕜 E where
  toFun x := f x
  map_add' x y := by simp
  map_smul' m x := by simp

@[simp]
lemma toBilinForm_apply (x y : E) : f.toBilinForm x y = f x y := rfl

section IsSymm

/-- A continuous bilinear form `f` is symmetric if for any `x, y` we have `f x y = f y x`. -/
structure IsSymm : Prop where
  map_symm : ∀ x y, f x y = f y x

lemma isSymm_def : f.IsSymm ↔ ∀ x y, f x y = f y x where
  mp := fun ⟨h⟩ ↦ h
  mpr h := ⟨h⟩

variable {f}

/-- Polarization identity: a symmetric continuous bilinear form can be expressed through values
it takes on the diagonal. -/
lemma IsSymm.polarization (x y : E) (hf : f.IsSymm) :
    f x y = (f (x + y) (x + y) - f x x - f y y) / 2 := by
  simp only [map_add, ContinuousLinearMap.add_apply]
  rw [hf.map_symm y x]
  ring

/-- A symmetric continuous bilinear form is characterized by the values it takes on the diagonal. -/
lemma ext_of_isSymm {g : ContinuousBilinForm 𝕜 E} (hf : IsSymm f) (hg : IsSymm g)
    (h : ∀ x, f x x = g x x) : f = g := by
  ext x y
  rw [hf.polarization, hg.polarization]
  simp_rw [h]

/-- A symmetric continuous bilinear form is characterized by the values it takes on the diagonal. -/
lemma ext_iff_of_isSymm {g : ContinuousBilinForm 𝕜 E} (hf : IsSymm f) (hg : IsSymm g) :
    f = g ↔ ∀ x, f x x = g x x where
  mp h := by simp [h]
  mpr := ext_of_isSymm hf hg

variable (f)

lemma isSymm_iff_basis : f.IsSymm ↔ ∀ i j, f (b i) (b j) = f (b j) (b i) where
  mp := fun ⟨h⟩ i j ↦ h _ _
  mpr := by
    refine fun h ↦ ⟨fun x y ↦ ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x ∈ Submodule.span 𝕜 (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : y ∈ Submodule.span 𝕜 (Set.range b))
    rw [← hx, ← hy]
    simp [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b₁ h₁ ↦ Finset.sum_congr rfl fun b₂ h₂ ↦ ?_)
    rw [mul_left_comm]
    obtain ⟨i, rfl⟩ := ix h₁
    obtain ⟨j, rfl⟩ := iy h₂
    rw [h]

end IsSymm

section Matrix

variable [Fintype n] [DecidableEq n]

section toMatrix

/-- A continuous bilinear map on a finite dimensional space can be represented by a matrix. -/
noncomputable def toMatrix : Matrix n n 𝕜 :=
  BilinForm.toMatrix b f.toBilinForm

@[simp]
lemma toMatrix_apply (i j : n) : f.toMatrix b i j = f (b i) (b j) := by
  simp [toMatrix]

lemma dotProduct_toMatrix_mulVec (x y : n → 𝕜) :
    x ⬝ᵥ (f.toMatrix b) *ᵥ y = f (b.equivFun.symm x) (b.equivFun.symm y) := by
  simp only [dotProduct, Matrix.mulVec_eq_sum, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply,
    Matrix.transpose_apply, toMatrix_apply, smul_eq_mul, Finset.mul_sum, Basis.equivFun_symm_apply,
    map_sum, map_smul, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
  ring

lemma apply_eq_dotProduct_toMatrix_mulVec (x y : E) :
    f x y = (b.repr x) ⬝ᵥ (f.toMatrix b) *ᵥ (b.repr y) := by
  nth_rw 1 [← b.sum_repr x, ← b.sum_repr y]
  simp [dotProduct, Matrix.mulVec_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
  ring

end toMatrix

section ofMatrix

variable (M : Matrix n n 𝕜) (b : Basis n 𝕜 E)

noncomputable
def ofMatrix : ContinuousBilinForm 𝕜 E :=
  haveI : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis b
  LinearMap.mkContinuous₂OfFiniteDimensional (M.toBilin b)

lemma ofMatrix_apply' (x y : E) : ofMatrix M b x y = M.toBilin b x y := rfl

open scoped Matrix in
lemma ofMatrix_apply (x y : E) :
    ofMatrix M b x y = b.repr x ⬝ᵥ M *ᵥ b.repr y := by
  simp [ofMatrix_apply', Matrix.toBilin_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma ofMatrix_basis (i j : n) : ofMatrix M b (b i) (b j) = M i j := by
  simp [ofMatrix_apply, Finsupp.single_eq_pi_single, Matrix.mulVec_single_one]

lemma toMatrix_ofMatrix : ofMatrix (f.toMatrix b) b = f := by
  ext x y
  rw [ofMatrix_apply, f.apply_eq_dotProduct_toMatrix_mulVec b]

lemma ofMatrix_toMatrix : (ofMatrix M b).toMatrix b = M := by
  ext i j
  rw [toMatrix_apply, ofMatrix_basis]

end ofMatrix

end Matrix

section IsPos

/-- A continuous bilinear map `f` is positive if for any `0 ≤ x`, `0 ≤ re (f x x)` -/
structure IsPos : Prop where
  nonneg_re_apply_self : ∀ x, 0 ≤ RCLike.re (f x x)

lemma isPos_def : f.IsPos ↔ ∀ x, 0 ≤ RCLike.re (f x x) where
  mp := fun ⟨h⟩ ↦ h
  mpr h := ⟨h⟩

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ContinuousBilinForm ℝ E)
    (b : Basis n ℝ E)

lemma isPos_def_real : f.IsPos ↔ ∀ x, 0 ≤ f x x := by simp [isPos_def]

variable {f} in
lemma IsPos.nonneg_apply_self (hf : IsPos f) (x : E) : 0 ≤ f x x := f.isPos_def_real.1 hf x

variable [Fintype n] [DecidableEq n]

lemma isSymm_iff_isHermitian_toMatrix : f.IsSymm ↔ (f.toMatrix b).IsHermitian := by
  rw [isSymm_iff_basis f b, Matrix.IsHermitian.ext_iff]
  simp [Eq.comm]

end Real

end IsPos

end RCLike

section Real

section NormedSpace

variable [NormedSpace ℝ E] (f : ContinuousBilinForm ℝ E) (b : Basis n ℝ E)

section IsPosSemidef

/-- A continuous bilinear map is positive semidefinite if it is symmetric and positive. We only
define it for the real field, because for the complex case we may want to consider sesquilinear
forms instead. -/
structure IsPosSemidef : Prop extends f.IsSymm, f.IsPos

variable {f}

lemma IsPosSemidef.isSymm (hf : IsPosSemidef f) : IsSymm f := hf.toIsSymm

lemma IsPosSemidef.isPos (hf : IsPosSemidef f) : IsPos f := hf.toIsPos

variable (f)

lemma isPosSemidef_iff : f.IsPosSemidef ↔ f.IsSymm ∧ f.IsPos where
  mp h := ⟨h.isSymm, h.isPos⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩

variable {f} [Fintype n] [DecidableEq n]

lemma isPosSemidef_iff_posSemidef_toMatrix : f.IsPosSemidef ↔ (f.toMatrix b).PosSemidef := by
  rw [isPosSemidef_iff, Matrix.PosSemidef]
  apply and_congr (f.isSymm_iff_isHermitian_toMatrix b)
  rw [isPos_def]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · rw [dotProduct_toMatrix_mulVec]
    exact h _
  · rw [apply_eq_dotProduct_toMatrix_mulVec f b]
    exact h _

end IsPosSemidef

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E]

open scoped InnerProductSpace

variable (E) in
/-- The inner product as continuous bilinear form. -/
protected noncomputable def inner : ContinuousBilinForm ℝ E :=
  letI f : LinearMap.BilinForm ℝ E := LinearMap.mk₂ ℝ
    (fun x y ↦ ⟪x, y⟫_ℝ)
    inner_add_left
    (fun c m n ↦ real_inner_smul_left m n c)
    inner_add_right
    (fun c m n ↦ real_inner_smul_right m n c)
  f.mkContinuous₂ 1 <| by
    intro x y
    simp only [LinearMap.mk₂_apply, Real.norm_eq_abs, one_mul, f]
    exact abs_real_inner_le_norm x y

@[simp]
lemma inner_apply (x y : E) : ContinuousBilinForm.inner E x y = ⟪x, y⟫_ℝ := rfl

lemma isPosSemidef_inner : IsPosSemidef (ContinuousBilinForm.inner E) where
  map_symm := by simp [real_inner_comm]
  nonneg_re_apply_self x := real_inner_self_nonneg

variable [Fintype n] [DecidableEq n] (b : OrthonormalBasis n ℝ E)

lemma inner_toMatrix_eq_one : (ContinuousBilinForm.inner E).toMatrix b.toBasis = 1 := by
  ext i j
  simp [Matrix.one_apply, b.inner_eq]

end InnerProductSpace

end Real

end ContinuousBilinForm
